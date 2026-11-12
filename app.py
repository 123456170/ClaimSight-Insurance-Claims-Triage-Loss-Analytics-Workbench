"""
ClaimSight — Insurance Claims Triage & Loss Analytics Workbench (Project 008)
============================================================================
Single-file Streamlit application. Synthetic data only. Decision support:
coverage and settlement decisions are reserved for authorized human roles.

Run on Windows PowerShell:
    python -m venv .venv                     # create isolated environment
    .\\.venv\\Scripts\\Activate.ps1            # activate it
    pip install -r requirements.txt          # install dependencies
    streamlit run app.py                     # launch (auto-seeds demo + starts simulation)

Architecture (all in this file, clearly separated):
    data layer (SQLite WAL)  -> domain engine (deterministic rules, versioned)
    -> ingestion/validation  -> services (triage, review, audit, export)
    -> Streamlit UI (8 workspaces) + auto-generated MP4 demo walkthrough.
"""
from __future__ import annotations

import hashlib
import io
import json
import math
import os
import random
import shutil
import sqlite3
import threading
import time
import uuid
from contextlib import closing
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Any

import numpy as np
import pandas as pd
import plotly.graph_objects as go
import streamlit as st

# ============================================================ constants
APP_NAME = "ClaimSight"
TAGLINE = "Insurance Claims Triage & Loss Analytics Workbench"
RULES_VERSION = "RULES-1.3.0"
SCHEMA_VERSION = "1.0.0"
FX_VERSION = "REF-2026.1"
SEED = 42
LATE_DAYS = 30
MAG_DENOM = 6.7  # log10(1+USD) denominator ≈ USD 5M ceiling

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "claimsight_data"
SRC_DIR = DATA_DIR / "source_files"
BKP_DIR = DATA_DIR / "backups"
VIDEO_DIR = DATA_DIR / "demo"
DB_PATH = DATA_DIR / "claimsight.db"
VIDEO_PATH = VIDEO_DIR / "claimsight_walkthrough.mp4"
for _d in (DATA_DIR, SRC_DIR, BKP_DIR, VIDEO_DIR):
    _d.mkdir(parents=True, exist_ok=True)

FX = {"USD": 1.0, "EUR": 1.08, "GBP": 1.27, "CAD": 0.74}  # static reference FX, documented
TYPE_CATALOG = {
    "Auto Collision":        dict(risk=0.45, hue="#38BDF8", mu=9.6,  sigma=0.8, weight=22, ref_limit=60_000),
    "Property Damage":       dict(risk=0.60, hue="#2DD4BF", mu=10.6, sigma=1.0, weight=18, ref_limit=500_000),
    "General Liability":     dict(risk=0.80, hue="#A78BFA", mu=11.0, sigma=1.1, weight=12, ref_limit=1_000_000),
    "Cargo & Transit":       dict(risk=0.55, hue="#FBBF24", mu=10.3, sigma=0.9, weight=10, ref_limit=400_000),
    "Cyber Incident":        dict(risk=0.90, hue="#F472B6", mu=11.6, sigma=1.2, weight=9,  ref_limit=2_000_000),
    "Business Interruption": dict(risk=0.80, hue="#FB923C", mu=11.9, sigma=1.1, weight=7,  ref_limit=2_000_000),
    "Workers Compensation":  dict(risk=0.70, hue="#4ADE80", mu=10.4, sigma=0.9, weight=13, ref_limit=300_000),
    "Equipment Breakdown":   dict(risk=0.50, hue="#60A5FA", mu=10.2, sigma=0.8, weight=9,  ref_limit=250_000),
}
TYPE_ALIASES = {k.lower(): k for k in TYPE_CATALOG}
BAND_ORDER = ["Critical", "High", "Medium", "Low"]
BAND_COLORS = {"Critical": "#FF4D6D", "High": "#FFB020", "Medium": "#38BDF8", "Low": "#34D399"}
BAND_EMOJI = {"Critical": "🔴", "High": "🟠", "Medium": "🔵", "Low": "🟢"}
SLA = {"Critical": 4, "High": 12, "Medium": 48, "Low": 96}
STATUSES = ["Intake", "Validated", "Correction", "In Review", "Approved", "Declined", "Settled", "Archived"]
STATUS_OPEN = ["Intake", "Validated", "Correction", "In Review"]
JURISDICTIONS = ["NY", "CA", "TX", "FL", "IL", "GA", "OH", "WA", "NC", "AZ", "ON-CA", "UK-LDN", "DE-BE"]
ADJUSTERS = ["Maya Chen", "Omar Haddad", "Priya Nair", "Lucas Meyer", "Sofia Rossi", "Ethan Brooks", "Ana Souza", "David Kim"]
INSUREDS = [
    "Harborview Logistics LLC", "Bluefin Payments Inc", "Crestline Manufacturing Co", "Northgate Treasury Services",
    "Lattice Fintech Ltd", "Ironbridge Freight Corp", "Solstice Retail Group", "Meridian Cold Storage",
    "Copperfield Lending Co", "Vantage Point Analytics", "Redwood Mutual Holdings", "Quayside Marine Terminals",
    "Beacon Ridge Energy", "Silverline Microfinance", "Oakmont Data Centers", "Pinnacle Foods Distribution",
    "Transatlantic Re Trading", "Cobalt Works Engineering", "Fairhaven Property Trust", "Nimbus Cloud Kitchens",
    "Granite Peak Outdoor Co", "Estuary Payments Network", "Lantern Health Partners", "Windrose Capital Ops",
]
DESCRIPTIONS = {
    "Auto Collision": ["Fleet vehicle rear-end collision on arterial road; third-party property damage reported.",
                       "Delivery van sideswipe during lane change; injuries under assessment."],
    "Property Damage": ["Storm-driven roof and water damage to warehouse; inventory exposure being inventoried.",
                        "Fire suppression discharge damaged finished goods in packing hall."],
    "General Liability": ["Client premises slip-and-fall; CCTV preserved and witness statements collected.",
                          "Alleged advisory error causing customer loss; reservation of rights issued."],
    "Cargo & Transit": ["Reefer container temperature excursion; perishable consignment partially rejected.",
                        "Palletized electronics damaged in transit; carrier liability under review."],
    "Cyber Incident": ["Ransomware containment and forensic engagement after credential compromise.",
                       "Business email compromise diverted supplier payment; recall attempted."],
    "Business Interruption": ["Utility outage halted production line for 36 hours; gross profit impact claimed.",
                              "Supplier failure stopped fulfillment; extra expense and lost revenue claimed."],
    "Workers Compensation": ["Warehouse associate lumbar strain during pallet handling; medicals attached.",
                             "Machine operator laceration; return-to-work plan drafted."],
    "Equipment Breakdown": ["Compressor failure halted cold chain; spoilage and repair costs claimed.",
                            "CNC spindle seizure; overtime outsourcing costs submitted."],
}
REQUIRED_IMPORT = ["claim_id", "policy_id", "insured_name", "loss_type", "loss_date", "reported_date", "reported_loss", "currency"]
COMPLETENESS_FIELDS = ["policy_id", "insured_name", "loss_type", "loss_date", "reported_date", "jurisdiction",
                       "currency", "reported_loss", "deductible", "policy_limit", "estimated_loss", "description", "adjuster"]
FLAG_LABELS = {
    "LATE_REPORT": f"Reported > {LATE_DAYS} days after loss",
    "LIMIT_BREACH": "Reported loss exceeds policy limit",
    "CONTRADICTORY_DATES": "Reported date precedes loss date",
    "DEDUCTIBLE_EXCEEDS_LOSS": "Deductible ≥ reported loss",
    "FUTURE_LOSS": "Loss date is in the future",
    "DUPLICATE_SUSPECT": "Same policy + loss date + amount as another claim",
    "MISSING_DOCS": "Completeness below 60%",
    "OUT_OF_RANGE": "Reported loss above USD 5M reference ceiling",
}
WEIGHTS = {"loss_ratio": 0.28, "magnitude": 0.24, "type_risk": 0.14, "completeness": 0.12, "delay": 0.10, "anomaly": 0.12}
FACTOR_LABELS = {
    "loss_ratio": "Loss / limit exposure", "magnitude": "Absolute loss magnitude", "type_risk": "Peril base risk",
    "completeness": "Completeness deficit", "delay": "Reporting delay", "anomaly": "Data-quality anomalies",
}
ROLES = ["Administrator", "Claims Analyst", "Senior Reviewer", "Read-only Stakeholder"]
ROLE_USER = {"Administrator": "Ava Sterling", "Claims Analyst": "Noah Reyes",
             "Senior Reviewer": "Dr. Lena Voss", "Read-only Stakeholder": "Sam Ito"}
ALL_PERMS = ["import", "manual_create", "edit", "triage", "archive", "review_decide", "settle",
             "override", "export_raw", "export_reports", "backup", "purge", "reset"]
PERMS = {
    "Administrator": set(ALL_PERMS),
    "Claims Analyst": {"import", "manual_create", "edit", "triage", "archive", "export_raw", "export_reports"},
    "Senior Reviewer": {"triage", "archive", "review_decide", "settle", "override", "export_reports"},
    "Read-only Stakeholder": {"export_reports"},
}
COLS = ["claim_id", "policy_id", "insured_name", "loss_type", "loss_date", "reported_date", "jurisdiction", "currency",
        "reported_loss", "estimated_loss", "deductible", "policy_limit", "description", "adjuster", "status",
        "coverage_status", "settlement_amount", "severity", "band", "completeness", "missing_fields", "flags",
        "components", "priority", "sla_hours", "source", "batch_id", "schema_version", "rules_version",
        "created_at", "updated_at"]
INSERT_CLAIM = f"INSERT INTO claims ({','.join(COLS)}) VALUES ({','.join(':' + c for c in COLS)})"

# ============================================================ utils
def now_utc() -> datetime: return datetime.now(timezone.utc)
def iso(dt: datetime) -> str: return dt.isoformat(timespec="seconds")
def dparse(v: Any) -> date:
    if isinstance(v, datetime): return v.date()
    if isinstance(v, date): return v
    s = str(v).strip()
    try: return date.fromisoformat(s[:10])
    except ValueError: return pd.to_datetime(s).date()
def dtparse(s: str) -> datetime:
    dt = datetime.fromisoformat(str(s))
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
def usd(amount: Any, ccy: Any) -> float:
    try: return float(amount) * FX.get(str(ccy or "USD").upper(), 1.0)
    except (TypeError, ValueError): return 0.0
def money(n: Any) -> str:
    try: return f"${float(n):,.0f}"
    except (TypeError, ValueError): return "—"
def compact(n: float) -> str:
    n = float(n or 0)
    if n >= 1e6: return f"${n/1e6:.2f}M"
    if n >= 1e3: return f"${n/1e3:.1f}k"
    return f"${n:,.0f}"
def ease(p: float) -> float:
    p = max(0.0, min(1.0, p)); return p * p * (3 - 2 * p)
def can(perm: str) -> bool: return perm in PERMS.get(st.session_state.role, set())
def require(perm: str) -> None:
    if not can(perm): raise PermissionError(f"Action '{perm}' is reserved for authorized roles.")

# ============================================================ data layer
def db() -> sqlite3.Connection:
    c = sqlite3.connect(DB_PATH, timeout=30)
    c.execute("PRAGMA journal_mode=WAL"); c.execute("PRAGMA busy_timeout=5000")
    return c
def q(sql: str, params: tuple = ()) -> pd.DataFrame:
    with closing(db()) as c: return pd.read_sql_query(sql, c, params=params)
def x(sql: str, params: tuple = ()) -> None:
    with closing(db()) as c:
        try: c.execute(sql, params); c.commit()
        finally: pass
def xm(sql: str, rows: list[dict]) -> None:
    with closing(db()) as c:
        try: c.executemany(sql, rows); c.commit()
        except Exception: c.rollback(); raise

def init_db() -> None:
    with closing(db()) as c:
        c.executescript("""
        CREATE TABLE IF NOT EXISTS claims (
            claim_id TEXT PRIMARY KEY, policy_id TEXT, insured_name TEXT, loss_type TEXT,
            loss_date TEXT, reported_date TEXT, jurisdiction TEXT, currency TEXT,
            reported_loss REAL, estimated_loss REAL, deductible REAL, policy_limit REAL,
            description TEXT, adjuster TEXT, status TEXT, coverage_status TEXT, settlement_amount REAL,
            severity REAL, band TEXT, completeness REAL, missing_fields TEXT, flags TEXT, components TEXT,
            priority REAL, sla_hours REAL, source TEXT, batch_id TEXT,
            schema_version TEXT, rules_version TEXT, created_at TEXT, updated_at TEXT);
        CREATE INDEX IF NOT EXISTS ix_claims_status ON claims(status);
        CREATE INDEX IF NOT EXISTS ix_claims_band ON claims(band);
        CREATE INDEX IF NOT EXISTS ix_claims_created ON claims(created_at);
        CREATE TABLE IF NOT EXISTS decisions (
            id INTEGER PRIMARY KEY AUTOINCREMENT, claim_id TEXT, kind TEXT, outcome TEXT,
            amount REAL, reason TEXT, actor TEXT, role TEXT, ts TEXT, rules_version TEXT);
        CREATE TABLE IF NOT EXISTS audit (
            id INTEGER PRIMARY KEY AUTOINCREMENT, ts TEXT, actor TEXT, role TEXT,
            action TEXT, claim_id TEXT, details TEXT);
        CREATE TABLE IF NOT EXISTS imports (
            batch_id TEXT PRIMARY KEY, filename TEXT, sha256 TEXT, rows_total INTEGER,
            rows_ok INTEGER, rows_rejected INTEGER, actor TEXT, ts TEXT, path TEXT);
        """)
        c.commit()

def log_audit(action: str, claim_id: str | None = None, details: Any = None,
              actor: str | None = None, role: str | None = None) -> None:
    x("INSERT INTO audit (ts,actor,role,action,claim_id,details) VALUES (?,?,?,?,?,?)",
      (iso(now_utc()), actor or ROLE_USER[st.session_state.role], role or st.session_state.role,
       action, claim_id, json.dumps(details) if isinstance(details, (dict, list)) else str(details or "")))

def add_decision(cid: str, kind: str, outcome: str, amount: float | None, reason: str,
                 actor: str | None = None, role: str | None = None, ts: str | None = None) -> None:
    x("INSERT INTO decisions (claim_id,kind,outcome,amount,reason,actor,role,ts,rules_version) VALUES (?,?,?,?,?,?,?,?,?)",
      (cid, kind, outcome, amount, reason, actor or ROLE_USER[st.session_state.role],
       role or st.session_state.role, ts or iso(now_utc()), RULES_VERSION))

# ============================================================ domain engine (deterministic, versioned)
def band_of(score: float) -> str:
    return "Critical" if score >= 80 else "High" if score >= 60 else "Medium" if score >= 40 else "Low"

def compute_completeness(rec: dict) -> tuple[float, list[str]]:
    missing = [f for f in COMPLETENESS_FIELDS
               if rec.get(f) is None or (isinstance(rec.get(f), float) and math.isnan(rec[f])) or str(rec.get(f)).strip() == ""]
    return round(100.0 * (len(COMPLETENESS_FIELDS) - len(missing)) / len(COMPLETENESS_FIELDS), 1), missing

def compute_flags(rec: dict, dup_keys: set | None = None) -> list[str]:
    flags: list[str] = []
    try:
        ld, rd = dparse(rec["loss_date"]), dparse(rec["reported_date"])
        today = now_utc().date()
        if (rd - ld).days > LATE_DAYS: flags.append("LATE_REPORT")
        if rd < ld: flags.append("CONTRADICTORY_DATES")
        if ld > today: flags.append("FUTURE_LOSS")
    except Exception:
        flags.append("CONTRADICTORY_DATES")
    loss = usd(rec.get("reported_loss"), rec.get("currency"))
    limit = rec.get("policy_limit")
    if limit and loss > usd(limit, rec.get("currency")): flags.append("LIMIT_BREACH")
    ded = rec.get("deductible")
    if ded is not None and not pd.isna(ded) and float(ded) >= float(rec.get("reported_loss") or 0):
        flags.append("DEDUCTIBLE_EXCEEDS_LOSS")
    if loss > 5_000_000: flags.append("OUT_OF_RANGE")
    if dup_keys is not None:
        key = (str(rec.get("policy_id")), str(rec.get("loss_date"))[:10], round(float(rec.get("reported_loss") or 0), 2))
        if key in dup_keys: flags.append("DUPLICATE_SUSPECT")
    comp, _ = compute_completeness(rec)
    if comp < 60: flags.append("MISSING_DOCS")
    return flags

def compute_severity(rec: dict, completeness: float, flags: list[str]) -> dict:
    """severity = 100 * Σ wᵢ·fᵢ  (weights documented in WEIGHTS; heuristic v1.3, needs domain sign-off)."""
    ccy = rec.get("currency") or "USD"
    reported = usd(rec.get("reported_loss"), ccy)
    cat = TYPE_CATALOG.get(rec.get("loss_type"), TYPE_CATALOG["Property Damage"])
    limit = usd(rec["policy_limit"], ccy) if rec.get("policy_limit") else cat["ref_limit"]
    try: delay_days = max(0, (dparse(rec["reported_date"]) - dparse(rec["loss_date"])).days)
    except Exception: delay_days = 0
    factors = {
        "loss_ratio": min(reported / max(limit, 1.0), 1.5) / 1.5,
        "magnitude": min(math.log10(1 + max(reported, 0)) / MAG_DENOM, 1.0),
        "type_risk": cat["risk"],
        "completeness": 1 - completeness / 100.0,
        "delay": min(delay_days / 60.0, 1.0),
        "anomaly": min(len(flags) / 4.0, 1.0),
    }
    components = [dict(key=k, label=FACTOR_LABELS[k], weight=WEIGHTS[k], factor=round(f, 4),
                       points=round(WEIGHTS[k] * f * 100, 2)) for k, f in factors.items()]
    score = round(max(0.0, min(100.0, sum(c["points"] for c in components))), 1)
    return dict(score=score, band=band_of(score), components=components,
                inputs=dict(reported_usd=round(reported, 2), limit_usd=round(limit, 2),
                            delay_days=delay_days, completeness=completeness, flags=len(flags)))

def assess(rec: dict, dup_keys: set | None = None) -> dict:
    comp, missing = compute_completeness(rec)
    flags = compute_flags(rec, dup_keys)
    sev = compute_severity(rec, comp, flags)
    band = sev["band"]
    rec.update(completeness=comp, missing_fields=json.dumps(missing), flags=json.dumps(flags),
               severity=sev["score"], band=band,
               components=json.dumps(dict(version=RULES_VERSION, factors=sev["components"], inputs=sev["inputs"])),
               sla_hours=SLA[band], priority=sev["score"])
    return rec

def live_enrich(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()
    if df.empty:
        for c in ["reported_usd", "age_h", "is_open", "sla_h", "breached", "priority_live", "flags_n", "missing_n"]:
            df[c] = []
        return df
    now = now_utc()
    df["reported_usd"] = [usd(v, c) for v, c in zip(df["reported_loss"], df["currency"])]
    df["age_h"] = [(now - dtparse(t)).total_seconds() / 3600 for t in df["created_at"]]
    df["is_open"] = df["status"].isin(STATUS_OPEN)
    df["sla_h"] = df["band"].map(SLA).fillna(48)
    df["breached"] = df["is_open"] & (df["age_h"] > df["sla_h"])
    df["priority_live"] = df["severity"] + (df["age_h"] / df["sla_h"] * 10).clip(upper=20)
    df.loc[~df["is_open"], "priority_live"] = df.loc[~df["is_open"], "severity"]
    df["flags_n"] = df["flags"].map(lambda s: len(json.loads(s or "[]")))
    df["missing_n"] = df["missing_fields"].map(lambda s: len(json.loads(s or "[]")))
    return df

def load_df() -> pd.DataFrame: return live_enrich(q("SELECT * FROM claims"))

# ============================================================ records, seed, simulation
def next_id(prefix: str = "CLM") -> str:
    return f"{prefix}-{now_utc():%y%m%d}-{uuid.uuid4().hex[:4].upper()}"

def prepare_record(raw: dict, source: str, batch_id: str | None = None,
                   created: datetime | None = None, dup_keys: set | None = None) -> dict:
    rec = {k: raw.get(k) for k in COLS}
    rec["claim_id"] = str(raw.get("claim_id") or next_id()).strip()
    rec.setdefault("status", "Validated")
    rec["status"] = raw.get("status") or "Validated"
    rec["coverage_status"] = raw.get("coverage_status") or "Pending"
    rec["settlement_amount"] = raw.get("settlement_amount")
    rec["source"] = source; rec["batch_id"] = batch_id
    rec["schema_version"] = SCHEMA_VERSION; rec["rules_version"] = RULES_VERSION
    created = created or now_utc()
    rec["created_at"] = iso(created); rec["updated_at"] = iso(created)
    return assess(rec, dup_keys)

def insert_claims(recs: list[dict]) -> None:
    if recs: xm(INSERT_CLAIM, [{k: r.get(k) for k in COLS} for r in recs])

def dup_key_set() -> set:
    d = q("SELECT policy_id, loss_date, reported_loss FROM claims")
    return {(str(a), str(b)[:10], round(float(c or 0), 2)) for a, b, c in d.itertuples(index=False)}

def make_claim(rng: random.Random, created: datetime, source: str, bias: float = 0.0,
               anomaly_rate: float = 0.07, force_critical: bool = False) -> dict:
    types = list(TYPE_CATALOG)
    weights = [TYPE_CATALOG[t]["weight"] * (1 + bias * TYPE_CATALOG[t]["risk"] * 2) for t in types]
    ltype = "Cyber Incident" if force_critical else rng.choices(types, weights=weights, k=1)[0]
    cat = TYPE_CATALOG[ltype]
    loss = round(rng.lognormvariate(cat["mu"], cat["sigma"]) * (1 + bias * 1.5), 2)
    limit = round(loss * rng.uniform(1.3, 6.0), -2)
    delay = min(int(rng.expovariate(1 / 7)), 75)
    ld = created.date() - timedelta(days=delay)
    rec = dict(claim_id=next_id("CLM-L" if source == "simulation" else "CLM"),
               policy_id=f"POL-{rng.randint(100000, 999999)}", insured_name=rng.choice(INSUREDS),
               loss_type=ltype, loss_date=ld.isoformat(), reported_date=created.date().isoformat(),
               jurisdiction=rng.choice(JURISDICTIONS),
               currency=rng.choices(list(FX), weights=[78, 9, 7, 6], k=1)[0],
               reported_loss=loss, estimated_loss=round(loss * rng.uniform(0.9, 1.6), 2),
               deductible=float(rng.choice([500, 1000, 2500, 5000, 10000])), policy_limit=limit,
               description=rng.choice(DESCRIPTIONS[ltype]), adjuster=rng.choice(ADJUSTERS))
    for f, p in [("description", 0.22), ("adjuster", 0.18), ("estimated_loss", 0.18),
                 ("policy_limit", 0.07), ("jurisdiction", 0.06), ("deductible", 0.05)]:
        if rng.random() < p: rec[f] = None
    if rng.random() < anomaly_rate:
        which = rng.choice(["breach", "late", "contradictory"])
        if which == "breach": rec["policy_limit"] = round(loss * rng.uniform(0.55, 0.9), 2)
        elif which == "late":
            rec["loss_date"] = (created.date() - timedelta(days=rng.randint(40, 75))).isoformat()
        else:
            rec["reported_date"] = (ld - timedelta(days=3)).isoformat(); rec["status"] = "Correction"
    if force_critical:
        rec.update(reported_loss=round(rng.uniform(400_000, 1_800_000), 2),
                   loss_date=(created.date() - timedelta(days=rng.randint(35, 55))).isoformat(),
                   description=None, adjuster=None, estimated_loss=None)
        rec["policy_limit"] = round(rec["reported_loss"] * rng.uniform(0.7, 1.0), 2)
    return rec

def seed_if_empty() -> None:
    if int(q("SELECT COUNT(*) AS n FROM claims")["n"][0]) > 0: return
    rng = random.Random(SEED)
    now = now_utc(); recs: list[dict] = []; keys: set = set()
    for i in range(160):
        days = rng.uniform(0, 21) if rng.random() < 0.6 else rng.uniform(21, 180)
        created = now - timedelta(days=days, hours=rng.uniform(0, 20), minutes=rng.uniform(0, 59))
        raw = make_claim(rng, created, "demo_seed", anomaly_rate=0.07)
        raw["claim_id"] = f"CLM-2026-{1000 + i}"
        age = days; r = rng.random()
        if age <= 2: status = "Intake" if r < 0.35 else "Validated"
        elif age <= 7: status = rng.choices(["Validated", "In Review", "Correction", "Intake", "Approved"], [30, 35, 15, 5, 15])[0]
        elif age <= 21: status = rng.choices(["In Review", "Validated", "Approved", "Settled", "Correction", "Declined"], [20, 15, 30, 20, 10, 5])[0]
        else: status = rng.choices(["Settled", "Archived", "Approved", "Declined", "In Review"], [45, 25, 15, 10, 5])[0]
        if "CONTRADICTORY_DATES" in compute_flags(raw): status = "Correction"
        raw["status"] = status
        raw["coverage_status"] = ("Approved" if status in ("Approved", "Settled") else
                                  "Declined" if status == "Declined" else
                                  ("Approved" if status == "Archived" and rng.random() < 0.7 else "Pending"))
        if status == "Archived" and raw["coverage_status"] != "Approved": raw["coverage_status"] = "Declined"
        rec = prepare_record(raw, "demo_seed", created=created, dup_keys=keys)
        keys.add((str(rec["policy_id"]), str(rec["loss_date"])[:10], round(float(rec["reported_loss"]), 2)))
        if status == "Settled":
            cap = max(0.0, float(rec["policy_limit"] or TYPE_CATALOG[rec["loss_type"]]["ref_limit"]) - float(rec["deductible"] or 0))
            amt = round(min(float(rec["reported_loss"]), cap) * rng.uniform(0.55, 0.95), 2)
            rec["settlement_amount"] = amt
            ts = iso(created + timedelta(hours=rng.uniform(6, 60)))
            add_decision(rec["claim_id"], "coverage", "Approved", None,
                         "Policy verified; peril covered under terms (seeded demo decision).",
                         actor="seed.engine", role="Senior Reviewer", ts=ts)
            add_decision(rec["claim_id"], "settlement", "Authorized", amt,
                         "Settlement within limit net of deductible (seeded demo decision).",
                         actor="seed.engine", role="Senior Reviewer", ts=ts)
            log_audit("coverage_decision", rec["claim_id"], "Approved", actor="seed.engine", role="Senior Reviewer")
            log_audit("settlement", rec["claim_id"], dict(amount=amt), actor="seed.engine", role="Senior Reviewer")
        elif raw["coverage_status"] in ("Approved", "Declined"):
            add_decision(rec["claim_id"], "coverage", raw["coverage_status"], None,
                         "Seeded demo coverage decision.", actor="seed.engine", role="Senior Reviewer",
                         ts=iso(created + timedelta(hours=12)))
            log_audit("coverage_decision", rec["claim_id"], raw["coverage_status"], actor="seed.engine", role="Senior Reviewer")
        recs.append(rec)
    clone_src = next(r for r in recs if r["status"] in STATUS_OPEN)
    clone = dict(clone_src); clone["claim_id"] = "CLM-2026-1999"
    clone = prepare_record(clone, "demo_seed", created=now - timedelta(hours=5), dup_keys=keys)
    clone["status"] = "Validated"; recs.append(clone)
    insert_claims(recs)
    log_audit("demo_seed", None, dict(claims=len(recs), seed=SEED), actor="seed.engine", role="System")

def spawn_batch(n: int, force_critical: bool = False) -> list[dict]:
    ss = st.session_state
    rng = random.Random()
    keys = dup_key_set(); out = []
    for _ in range(n):
        raw = make_claim(rng, now_utc(), "simulation", bias=ss.sim_bias,
                         anomaly_rate=ss.sim_anomaly, force_critical=force_critical)
        rec = prepare_record(raw, "simulation", dup_keys=keys)
        if ss.sim_autotriage and rec["band"] in ("Critical", "High"):
            rec["status"] = "In Review"
            log_audit("auto_triage", rec["claim_id"], f"Auto-routed to review ({rec['band']})", actor="triage.bot", role="System")
        insert_claims([rec])
        log_audit("intake_sim", rec["claim_id"], dict(band=rec["band"], usd=round(usd(rec["reported_loss"], rec["currency"])),
                                                    force_critical=force_critical), actor="intake.sim", role="System")
        ss.arrivals.insert(0, dict(t=now_utc().strftime("%H:%M:%S"), id=rec["claim_id"], type=rec["loss_type"],
                                   band=rec["band"], usd=usd(rec["reported_loss"], rec["currency"])))
        out.append(rec)
    ss.arrivals = ss.arrivals[:14]
    crit = [r for r in out if r["band"] == "Critical"]
    if crit and time.monotonic() - ss.last_crit_toast > 20:
        ss.last_crit_toast = time.monotonic()
        st.toast(f"🚨 Critical claim {crit[0]['claim_id']} entered the queue", icon="🚨")
    return out

# ============================================================ samples + validation + import
def sample_valid_df() -> pd.DataFrame:
    t = now_utc().date(); rows = []
    base = [("Auto Collision", 18400, 60000), ("Property Damage", 96500, 500000), ("Cyber Incident", 310000, 1500000),
            ("Cargo & Transit", 42750, 400000), ("General Liability", 125000, 1000000), ("Workers Compensation", 23800, 300000),
            ("Business Interruption", 410000, 2000000), ("Equipment Breakdown", 31200, 250000),
            ("Property Damage", 55200, 500000), ("Auto Collision", 9900, 60000)]
    for i, (lt, loss, lim) in enumerate(base):
        rows.append(dict(claim_id=f"CLM-S-{1001+i}", policy_id=f"POL-{700100+i}", insured_name=INSUREDS[i],
                         loss_type=lt, loss_date=(t - timedelta(days=12 + i)).isoformat(),
                         reported_date=(t - timedelta(days=2 + i % 3)).isoformat(),
                         jurisdiction=JURISDICTIONS[i % len(JURISDICTIONS)], currency="USD",
                         reported_loss=loss, estimated_loss=round(loss * 1.2, 2), deductible=2500,
                         policy_limit=lim, description=DESCRIPTIONS[lt][0] if i % 4 else None,
                         adjuster=ADJUSTERS[i % len(ADJUSTERS)] if i % 3 else None))
    return pd.DataFrame(rows)

def sample_bad_df() -> pd.DataFrame:
    t = now_utc().date()
    good = dict(policy_id="POL-800001", insured_name="Test Co", loss_type="Auto Collision",
                loss_date=(t - timedelta(days=10)).isoformat(), reported_date=(t - timedelta(days=2)).isoformat(),
                jurisdiction="NY", currency="USD", reported_loss=10000, deductible=1000, policy_limit=60000)
    rows = []
    def mk(cid, **kw): r = dict(good); r["claim_id"] = cid; r.update(kw); rows.append(r)
    mk("CLM-S-2001"); mk("CLM-S-2001")  # duplicate key
    mk("CLM-S-2002", loss_date="2026-13-45")
    mk("CLM-S-2003", reported_loss=-500)
    mk("CLM-S-2004", loss_type="Alien Abduction")
    mk("CLM-S-2005", policy_id=None)
    mk("CLM-S-2006", currency="BTC")
    mk("CLM-S-2007", loss_date=(t + timedelta(days=10)).isoformat(), reported_date=(t + timedelta(days=11)).isoformat())
    mk("CLM-S-2008", reported_date=(t - timedelta(days=20)).isoformat())
    return pd.DataFrame(rows)

def _amount(v: Any) -> float | None:
    if v is None or (isinstance(v, float) and math.isnan(v)) or str(v).strip() == "": return None
    return float(str(v).replace(",", "").replace("$", "").strip())

def _row_errors(rec: dict) -> tuple[list[str], dict]:
    errs: list[str] = []; norm = dict(rec); today = now_utc().date()
    for f in REQUIRED_IMPORT:
        v = rec.get(f)
        if v is None or (isinstance(v, float) and math.isnan(v)) or str(v).strip() == "":
            errs.append(f"'{f}' is required but missing")
    lt = TYPE_ALIASES.get(str(rec.get("loss_type") or "").strip().lower())
    if rec.get("loss_type") and not lt:
        errs.append(f"loss_type '{rec['loss_type']}' not in catalog — use one of: {', '.join(TYPE_CATALOG)}")
    if lt: norm["loss_type"] = lt
    ccy = str(rec.get("currency") or "").strip().upper()
    if rec.get("currency") and ccy not in FX:
        errs.append(f"currency '{rec['currency']}' unsupported — allowed: {', '.join(FX)}")
    norm["currency"] = ccy or None
    for f in ["reported_loss", "estimated_loss", "deductible", "policy_limit"]:
        try: norm[f] = _amount(rec.get(f))
        except ValueError: errs.append(f"'{f}' must be numeric (got '{rec.get(f)}'); remove symbols/text")
    if norm.get("reported_loss") is not None and norm["reported_loss"] <= 0:
        errs.append("reported_loss must be a positive amount")
    ld = rd = None
    for f in ["loss_date", "reported_date"]:
        if rec.get(f) not in (None, "") and not (isinstance(rec.get(f), float) and math.isnan(rec.get(f))):
            try:
                d = dparse(rec[f]); norm[f] = d.isoformat()
                if f == "loss_date": ld = d
                else: rd = d
            except Exception: errs.append(f"'{f}' is not a valid date (use YYYY-MM-DD)")
    if ld and ld > today: errs.append("loss_date is in the future — correct the date or hold the record")
    if ld and rd and rd < ld: errs.append("reported_date precedes loss_date — contradictory dates")
    for f in ["claim_id", "policy_id", "insured_name", "jurisdiction", "description", "adjuster"]:
        v = rec.get(f)
        norm[f] = None if v is None or (isinstance(v, float) and math.isnan(v)) else str(v).strip() or None
    return errs, norm

def validate_dataframe(df: pd.DataFrame, check_db: bool = True) -> tuple[list[dict], pd.DataFrame, pd.DataFrame, list[str]]:
    df = df.copy()
    df.columns = [str(c).strip().lower().replace(" ", "_") for c in df.columns]
    fatal = [f"Missing required column: '{c}'" for c in REQUIRED_IMPORT if c not in df.columns]
    if fatal: return [], pd.DataFrame(), pd.DataFrame(), fatal
    db_ids = set(q("SELECT claim_id FROM claims")["claim_id"]) if check_db else set()
    keys = dup_key_set() if check_db else set()
    seen: set = set(); ok: list[dict] = []; err_rows: list[dict] = []; preview: list[dict] = []
    for i, row in df.iterrows():
        rec = row.to_dict()
        errs, norm = _row_errors(rec)
        cid = str(norm.get("claim_id") or "")
        if cid and cid in seen: errs.append(f"duplicate claim_id '{cid}' within file")
        if cid and cid in db_ids: errs.append(f"claim_id '{cid}' already exists in database — existing record preserved")
        if cid: seen.add(cid)
        warnings: list[str] = []
        if not errs:
            fl = compute_flags(norm, keys)
            warnings = [FLAG_LABELS[f] for f in fl]
            ok.append(norm)
        else:
            err_rows.append(dict(row=int(i) + 2, claim_id=cid, errors="; ".join(errs)))
        preview.append(dict(Row=int(i) + 2, claim_id=cid, Type=norm.get("loss_type"),
                            Reported=norm.get("reported_loss"),
                            Result="❌ rejected" if errs else "✅ ok",
                            Errors="; ".join(errs), Warnings="; ".join(warnings)))
    return ok, pd.DataFrame(err_rows), pd.DataFrame(preview), []

def commit_import(file_bytes: bytes, filename: str, ok_recs: list[dict], total: int, rejected: int) -> bool:
    require("import")
    sha = hashlib.sha256(file_bytes).hexdigest()
    if not q("SELECT batch_id FROM imports WHERE sha256=?", (sha,)).empty:
        st.warning("This exact file was already imported (checksum match). Re-import blocked — existing records are safe.")
        return False
    batch = uuid.uuid4().hex[:8]
    source = "xlsx_import" if filename.lower().endswith(".xlsx") else "csv_import"
    keys = dup_key_set()
    recs = [prepare_record(r, source, batch_id=batch, dup_keys=keys) for r in ok_recs]
    stored = SRC_DIR / f"{sha[:16]}_{filename}"
    stored.write_bytes(file_bytes)
    with closing(db()) as c:
        try:
            c.execute("BEGIN")
            c.executemany(INSERT_CLAIM, [{k: r.get(k) for k in COLS} for r in recs])
            c.execute("INSERT INTO imports VALUES (?,?,?,?,?,?,?,?,?)",
                      (batch, filename, sha, total, len(recs), rejected, ROLE_USER[st.session_state.role], iso(now_utc()), str(stored)))
            c.commit()
        except sqlite3.IntegrityError:
            c.rollback(); st.error("Import aborted safely — a key conflict occurred and no records were changed."); return False
    log_audit("import_batch", None, dict(batch=batch, file=filename, ok=len(recs), rejected=rejected, sha256=sha[:16]))
    st.toast(f"✅ Imported {len(recs)} claims (batch {batch})", icon="📥")
    return True

# ============================================================ visual language
def inject_css() -> None:
    st.markdown("""<style>
[data-testid="stApp"]{background:
 radial-gradient(1200px 600px at 8% -5%,rgba(45,212,191,.10),transparent 60%),
 radial-gradient(1000px 700px at 100% 10%,rgba(167,139,250,.10),transparent 55%),
 radial-gradient(900px 500px at 50% 110%,rgba(56,189,248,.07),transparent 60%),
 linear-gradient(180deg,#070D1A 0%,#0A1322 100%);color:#E8F1F8;}
[data-testid="stHeader"]{background:transparent;pointer-events:none;}
[data-testid="stHeader"] *{pointer-events:auto;}
#MainMenu,footer,[data-testid="stDecoration"]{visibility:hidden;}
[data-testid="stMainBlockContainer"]{padding-top:1rem;max-width:1560px;}
[data-testid="stSidebar"]{background:linear-gradient(180deg,#0A1424,#081020);border-right:1px solid rgba(94,234,212,.12);}
*::-webkit-scrollbar{width:10px;height:10px}
*::-webkit-scrollbar-track{background:#0A1424}
*::-webkit-scrollbar-thumb{background:linear-gradient(180deg,#14B8A6,#38BDF8);border-radius:8px;border:2px solid #0A1424}
*::-webkit-scrollbar-thumb:hover{background:#2DD4BF}
*{scrollbar-width:thin;scrollbar-color:#14B8A6 #0A1424;}
[data-testid="stTabs"] [data-baseweb="tab-list"]{position:sticky;top:0;z-index:40;background:rgba(7,13,26,.92);
 backdrop-filter:blur(10px);border-bottom:1px solid rgba(94,234,212,.15);gap:2px;padding:4px 2px;}
[data-baseweb="tab"]{font-weight:600;letter-spacing:.02em;color:#8FA6BC;}
[data-baseweb="tab"][aria-selected="true"]{color:#2DD4BF;}
[data-baseweb="tab-highlight"]{background:#2DD4BF;}
.stButton>button,.stDownloadButton>button,[data-testid="stFormSubmitButton"]>button{
 background:linear-gradient(180deg,rgba(45,212,191,.12),rgba(56,189,248,.08));
 border:1px solid rgba(45,212,191,.35);color:#DFF7F3;border-radius:10px;font-weight:600;transition:all .15s;}
.stButton>button:hover,.stDownloadButton>button:hover,[data-testid="stFormSubmitButton"]>button:hover{
 border-color:#2DD4BF;box-shadow:0 0 14px rgba(45,212,191,.25);transform:translateY(-1px);color:#fff;}
.stButton>button:disabled{opacity:.4;}
[data-testid="stBaseButton-primary"],[data-testid="stFormSubmitButton"] button[kind="primaryFormSubmit"]{
 background:linear-gradient(90deg,#0D9488,#0284C7)!important;border:none!important;color:#fff!important;}
input,textarea,[data-baseweb="select"]>div{background:#0E1B2E!important;border-color:rgba(148,184,220,.2)!important;
 color:#E8F1F8!important;border-radius:10px!important;}
[data-testid="stDataFrame"]{border:1px solid rgba(94,234,212,.14);border-radius:12px;}
[data-testid="stExpander"]{border:1px solid rgba(94,234,212,.12);border-radius:12px;background:rgba(14,27,46,.5);}
.cs-hero{border:1px solid rgba(45,212,191,.25);background:linear-gradient(120deg,rgba(13,148,136,.16),rgba(2,132,199,.10) 45%,rgba(139,92,246,.12));
 border-radius:16px;padding:16px 22px;display:flex;justify-content:space-between;align-items:center;gap:16px;
 box-shadow:0 10px 40px rgba(2,132,199,.12);margin-bottom:10px;}
.cs-title{font-size:1.85rem;font-weight:800;background:linear-gradient(90deg,#5EEAD4,#38BDF8 55%,#A78BFA);
 -webkit-background-clip:text;background-clip:text;color:transparent;line-height:1.15;}
.cs-sub{color:#8FA6BC;font-size:.9rem;}
.cs-chip{display:inline-flex;align-items:center;gap:6px;padding:4px 10px;border-radius:999px;
 border:1px solid rgba(148,184,220,.25);background:rgba(14,27,46,.7);font-size:.7rem;font-weight:700;
 letter-spacing:.06em;color:#B9CBDD;margin:2px;}
.chip-teal{border-color:rgba(45,212,191,.5);color:#5EEAD4}.chip-amber{border-color:rgba(255,176,32,.5);color:#FFCF7D}
.chip-red{border-color:rgba(255,77,109,.5);color:#FF8FA3}.chip-violet{border-color:rgba(167,139,250,.5);color:#C4B5FD}
.cs-kpis{display:grid;grid-template-columns:repeat(6,1fr);gap:10px;margin:6px 0;}
@media(max-width:1100px){.cs-kpis{grid-template-columns:repeat(3,1fr);}}
@media(max-width:640px){.cs-kpis{grid-template-columns:repeat(2,1fr);}.cs-hero{flex-direction:column;align-items:flex-start;}}
.cs-kpi{background:linear-gradient(180deg,rgba(16,30,51,.9),rgba(11,21,38,.9));border:1px solid rgba(148,184,220,.14);
 border-left:3px solid var(--acc,#2DD4BF);border-radius:12px;padding:10px 12px;}
.cs-kpi .l{font-size:.66rem;letter-spacing:.08em;color:#8FA6BC;font-weight:700;text-transform:uppercase;}
.cs-kpi .v{font-size:1.5rem;font-weight:800;color:#F2F8FD;line-height:1.25;}
.cs-kpi .s{font-size:.72rem;color:#7E96AC;}
.badge{padding:2px 9px;border-radius:999px;font-size:.72rem;font-weight:800;letter-spacing:.03em;white-space:nowrap;}
.b-Critical{background:rgba(255,77,109,.15);color:#FF6B85;border:1px solid rgba(255,77,109,.5);box-shadow:0 0 12px rgba(255,77,109,.25);}
.b-High{background:rgba(255,176,32,.13);color:#FFB020;border:1px solid rgba(255,176,32,.5);}
.b-Medium{background:rgba(56,189,248,.12);color:#38BDF8;border:1px solid rgba(56,189,248,.5);}
.b-Low{background:rgba(52,211,153,.12);color:#34D399;border:1px solid rgba(52,211,153,.5);}
.cs-feed{display:flex;flex-direction:column;gap:6px;max-height:265px;overflow-y:auto;padding-right:4px;}
.cs-row{display:flex;align-items:center;gap:8px;background:rgba(14,27,46,.65);border:1px solid rgba(148,184,220,.12);
 border-radius:10px;padding:6px 10px;font-size:.8rem;animation:csIn .35s ease;}
@keyframes csIn{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:none}}
.cs-dot{width:9px;height:9px;border-radius:50%;flex:none;}
.pulse{animation:pulse 1.6s infinite;}
@keyframes pulse{0%,100%{opacity:1}50%{opacity:.35}}
.mono{font-family:Consolas,'DejaVu Sans Mono',monospace;font-size:.78rem;color:#9FB6CC;}
.cs-amt{margin-left:auto;font-weight:700;color:#E8F1F8;}
.cs-alert{border-radius:10px;padding:8px 12px;font-size:.83rem;border:1px solid;margin:4px 0;}
.a-warn{background:rgba(255,176,32,.08);border-color:rgba(255,176,32,.4);color:#FFCF7D;}
.a-bad{background:rgba(255,77,109,.08);border-color:rgba(255,77,109,.45);color:#FF8FA3;}
.a-info{background:rgba(56,189,248,.08);border-color:rgba(56,189,248,.4);color:#7DD3FC;}
.a-ok{background:rgba(52,211,153,.08);border-color:rgba(52,211,153,.4);color:#6EE7B7;}
.cs-section{font-size:1.02rem;font-weight:800;color:#DFF7F3;margin:.5rem 0 .3rem;border-left:3px solid #2DD4BF;padding-left:10px;}
.cs-facts{width:100%;border-collapse:collapse;font-size:.82rem;}
.cs-facts td{padding:4px 6px;border-bottom:1px dashed rgba(148,184,220,.12);}
.cs-facts td:first-child{color:#8FA6BC;width:44%;}
.cs-lock{background:rgba(167,139,250,.08);border:1px solid rgba(167,139,250,.4);color:#C4B5FD;border-radius:12px;
 padding:10px 14px;font-size:.85rem;margin:6px 0;}
.cs-card{background:rgba(14,27,46,.6);border:1px solid rgba(148,184,220,.14);border-radius:12px;padding:12px 14px;margin:4px 0;}
.cs-mini{font-size:.75rem;color:#7E96AC;}
.cs-footer{margin-top:26px;padding:12px;border-top:1px solid rgba(148,184,220,.12);color:#6E859B;font-size:.74rem;text-align:center;}
</style>""", unsafe_allow_html=True)

def badge(band: str) -> str: return f'<span class="badge b-{band}">{band}</span>'
def section(title: str) -> None: st.markdown(f'<div class="cs-section">{title}</div>', unsafe_allow_html=True)

def kpi_html(tiles: list[dict]) -> str:
    cells = "".join(f'<div class="cs-kpi" style="--acc:{t["hue"]}"><div class="l">{t["label"]}</div>'
                    f'<div class="v">{t["value"]}</div><div class="s">{t["sub"]}</div></div>' for t in tiles)
    return f'<div class="cs-kpis">{cells}</div>'

def feed_html(rows: list[dict]) -> str:
    if not rows: return '<div class="cs-mini">Waiting for first intake event…</div>'
    out = "".join(f'<div class="cs-row"><span class="cs-dot pulse" style="background:{BAND_COLORS[r["band"]]}"></span>'
                  f'<span class="mono">{r["t"]}</span><span class="mono">{r["id"]}</span>'
                  f'<span style="color:#B9CBDD">{r["type"]}</span><span class="cs-amt">{compact(r["usd"])}</span></div>'
                  for r in rows)
    return f'<div class="cs-feed">{out}</div>'

def style_fig(fig: go.Figure, h: int = 300) -> go.Figure:
    fig.update_layout(height=h, paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(16,30,51,.45)",
                      font=dict(color="#C9D6E3", family="Segoe UI", size=12),
                      margin=dict(l=10, r=10, t=30, b=10),
                      legend=dict(orientation="h", y=1.12, x=0, bgcolor="rgba(0,0,0,0)"),
                      hoverlabel=dict(bgcolor="#0B1526", font_color="#E8F1F8"))
    fig.update_xaxes(gridcolor="rgba(148,184,220,.12)", zerolinecolor="rgba(148,184,220,.2)")
    fig.update_yaxes(gridcolor="rgba(148,184,220,.12)", zerolinecolor="rgba(148,184,220,.2)")
    return fig

def hero() -> None:
    ss = st.session_state
    sim_chip = ('<span class="cs-chip chip-teal">● SIMULATION LIVE</span>' if ss.sim_running
                else '<span class="cs-chip chip-amber">⏸ SIMULATION PAUSED</span>')
    vs = video_state()
    vid_chip = ('<span class="cs-chip chip-violet">🎬 WALKTHROUGH READY</span>' if vs == "ready"
                else '<span class="cs-chip">🎬 RENDERING WALKTHROUGH…</span>' if vs == "rendering"
                else '<span class="cs-chip">🎬 DEMO STUDIO</span>')
    st.markdown(f"""<div class="cs-hero">
<div style="display:flex;align-items:center;gap:14px;">
<svg width="46" height="46" viewBox="0 0 48 48"><defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1">
<stop offset="0" stop-color="#2DD4BF"/><stop offset=".55" stop-color="#38BDF8"/><stop offset="1" stop-color="#A78BFA"/>
</linearGradient></defs><path d="M24 3 42 10v12c0 11-7.6 19.4-18 23C13.6 41.4 6 33 6 22V10Z"
fill="none" stroke="url(#lg)" stroke-width="2.6"/>
<path d="M11 26h7l3-8 5 14 3-6h8" fill="none" stroke="url(#lg)" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"/></svg>
<div><div class="cs-title">{APP_NAME}</div><div class="cs-sub">{TAGLINE}</div></div></div>
<div style="text-align:right;max-width:420px;">
<span class="cs-chip chip-amber">SYNTHETIC DATA</span><span class="cs-chip">{RULES_VERSION}</span>
<span class="cs-chip chip-teal">👤 {ROLE_USER[ss.role]} · {ss.role}</span>{sim_chip}{vid_chip}
<div class="cs-mini" style="margin-top:4px;">Coverage &amp; settlement decisions require authorized human approval.</div>
</div></div>""", unsafe_allow_html=True)

# ============================================================ explanation panel
def render_explanation(rec: dict) -> None:
    comp = json.loads(rec.get("components") or "{}")
    factors = comp.get("factors", [])
    inputs = comp.get("inputs", {})
    overridden = any(f.get("key") == "override" for f in factors)
    if factors:
        core = [f for f in factors if f.get("key") != "override"]
        fig = go.Figure(go.Bar(orientation="h", y=[f["label"] for f in core][::-1], x=[f["points"] for f in core][::-1],
                               marker=dict(color=["#2DD4BF", "#38BDF8", "#A78BFA", "#FBBF24", "#F472B6", "#FB923C"][:len(core)][::-1]),
                               text=[f'{f["points"]:.1f} pts' for f in core][::-1], textposition="outside"))
        fig.update_layout(title=dict(text=f'Severity {rec["severity"]} / 100 · {rec["band"]}' + (" · OVERRIDDEN" if overridden else ""),
                                     font=dict(size=14)))
        st.plotly_chart(style_fig(fig, 250), width="stretch", key=f"expl_{rec['claim_id']}_{rec['updated_at']}")
    flags = json.loads(rec.get("flags") or "[]"); missing = json.loads(rec.get("missing_fields") or "[]")
    if flags:
        st.markdown("".join(f'<span class="cs-chip chip-red">⚠ {FLAG_LABELS.get(f, f)}</span>' for f in flags), unsafe_allow_html=True)
    if missing:
        st.markdown("".join(f'<span class="cs-chip chip-amber">📄 missing: {f}</span>' for f in missing), unsafe_allow_html=True)
    st.caption(f"Inputs → reported {money(inputs.get('reported_usd'))} · limit {money(inputs.get('limit_usd'))} · "
               f"delay {inputs.get('delay_days', 0)}d · completeness {inputs.get('completeness', rec.get('completeness'))}% · "
               f"flags {inputs.get('flags', len(flags))} · engine {comp.get('version', RULES_VERSION)} · FX {FX_VERSION}")
    with st.expander("🧮 Hand-checkable arithmetic (weight × factor × 100)"):
        st.dataframe(pd.DataFrame(factors)[["label", "weight", "factor", "points"]], hide_index=True, width="stretch")
        st.caption("severity = Σ points, clamped to [0,100]. Bands: ≥80 Critical · ≥60 High · ≥40 Medium · else Low. "
                   "Heuristic weights are versioned and require domain sign-off before production use.")
    dup = q("SELECT COUNT(*) n FROM claims WHERE policy_id=? AND loss_date=? AND reported_loss=? AND claim_id<>?",
            (rec.get("policy_id"), rec.get("loss_date"), rec.get("reported_loss"), rec["claim_id"]))
    if int(dup["n"][0]) > 0:
        st.markdown('<div class="cs-alert a-bad">Possible duplicate: another claim shares policy + loss date + amount.</div>', unsafe_allow_html=True)
    hist = q("SELECT ts, kind, outcome, amount, actor, role, reason FROM decisions WHERE claim_id=? ORDER BY ts DESC", (rec["claim_id"],))
    if not hist.empty:
        section("Decision history")
        st.dataframe(hist, hide_index=True, width="stretch", height=min(200, 40 + 35 * len(hist)))
    st.caption(f"Lineage → source: {rec.get('source')} · batch: {rec.get('batch_id') or '—'} · schema {rec.get('schema_version')} · "
               f"created {rec.get('created_at')} · coverage status: {rec.get('coverage_status')}")

def claim_facts_html(rec: dict) -> str:
    rows = [("Insured", rec.get("insured_name")), ("Policy", rec.get("policy_id")), ("Peril", rec.get("loss_type")),
            ("Loss / Reported", f'{rec.get("loss_date")} → {rec.get("reported_date")}'),
            ("Jurisdiction", rec.get("jurisdiction") or "—"),
            ("Reported loss", f'{money(rec.get("reported_loss"))} {rec.get("currency")}'),
            ("Estimated", money(rec.get("estimated_loss")) if rec.get("estimated_loss") else "—"),
            ("Deductible / Limit", f'{money(rec.get("deductible"))} / {money(rec.get("policy_limit"))}'),
            ("Adjuster", rec.get("adjuster") or "Unassigned"), ("Status", rec.get("status")),
            ("Settlement", money(rec.get("settlement_amount")) if rec.get("settlement_amount") else "—")]
    body = "".join(f"<tr><td>{k}</td><td>{v if v is not None else '—'}</td></tr>" for k, v in rows)
    return f'<table class="cs-facts">{body}</table>'

# ============================================================ mutations
def set_status(ids: list[str], new: str, action: str = "status_change") -> None:
    require("triage")
    for cid in ids:
        x("UPDATE claims SET status=?, updated_at=? WHERE claim_id=?", (new, iso(now_utc()), cid))
        log_audit(action, cid, f"→ {new}")
    st.toast(f"✅ {len(ids)} claim(s) → {new}", icon="🚦")

def archive_ids(ids: list[str]) -> None:
    require("archive")
    prev = q("SELECT claim_id,status FROM claims")
    pm = dict(zip(prev["claim_id"], prev["status"]))
    st.session_state.undo = dict(kind="status", label=f"Archive {len(ids)} claim(s)",
                                 items=[(cid, pm.get(cid, "Validated")) for cid in ids])
    for cid in ids:
        x("UPDATE claims SET status='Archived', updated_at=? WHERE claim_id=?", (iso(now_utc()), cid))
        log_audit("archive", cid, f"{pm.get(cid)} → Archived")
    st.toast(f"🗄️ Archived {len(ids)} claim(s) — undo available", icon="🗄️")

def apply_undo() -> None:
    u = st.session_state.get("undo")
    if not u: return
    require("edit" if u["kind"] == "adjuster" else "triage")
    col = "adjuster" if u["kind"] == "adjuster" else "status"
    for cid, prev in u["items"]:
        x(f"UPDATE claims SET {col}=?, updated_at=? WHERE claim_id=?", (prev, iso(now_utc()), cid))
        log_audit("undo", cid, f"restored {col}={prev}")
    st.session_state.undo = None
    st.toast(f"↩ Undone: {u['label']}", icon="↩")

def auto_balance() -> None:
    require("triage")
    df = load_df(); op = df[df["is_open"]]
    loads = {a: int((op["adjuster"] == a).sum()) for a in ADJUSTERS}
    targets = op[(op["adjuster"].isna() | (op["adjuster"] == "")) & op["band"].isin(["Critical", "High"])] \
        .sort_values("priority_live", ascending=False)
    if targets.empty: st.info("No unassigned Critical/High claims to balance."); return
    items = []
    for _, r in targets.iterrows():
        a = min(loads, key=loads.get); loads[a] += 1
        x("UPDATE claims SET adjuster=?, updated_at=? WHERE claim_id=?", (a, iso(now_utc()), r["claim_id"]))
        log_audit("assign", r["claim_id"], f"auto-balance → {a}")
        items.append((r["claim_id"], None))
    st.session_state.undo = dict(kind="adjuster", label=f"Auto-balance {len(items)} assignments", items=items)
    st.toast(f"⚖️ Balanced {len(items)} assignments — undo available", icon="⚖️")

def submit_decision(rec: dict, outcome: str, settle: bool, amount: float, reason: str) -> None:
    require("review_decide")
    if len(reason.strip()) < 10:
        st.error("A decision reason of at least 10 characters is required for the audit trail."); return
    cid = rec["claim_id"]; ts = iso(now_utc())
    cap = max(0.0, float(rec.get("policy_limit") or TYPE_CATALOG[rec["loss_type"]]["ref_limit"]) - float(rec.get("deductible") or 0))
    if outcome == "Approve coverage":
        if settle:
            require("settle")
            if not (0 < amount <= cap + 1e-6):
                st.error(f"Settlement must be > 0 and ≤ {money(cap)} {rec['currency']} (limit net of deductible)."); return
            x("UPDATE claims SET coverage_status='Approved', status='Settled', settlement_amount=?, updated_at=? WHERE claim_id=?",
              (amount, ts, cid))
            add_decision(cid, "coverage", "Approved", None, reason)
            add_decision(cid, "settlement", "Authorized", amount, reason)
            log_audit("coverage_decision", cid, "Approved"); log_audit("settlement", cid, dict(amount=amount, reason=reason))
            st.toast(f"✅ Coverage approved · settlement {money(amount)} authorized", icon="✅")
        else:
            x("UPDATE claims SET coverage_status='Approved', status='Approved', updated_at=? WHERE claim_id=?", (ts, cid))
            add_decision(cid, "coverage", "Approved", None, reason); log_audit("coverage_decision", cid, "Approved")
            st.toast("✅ Coverage approved", icon="✅")
    elif outcome == "Decline coverage":
        x("UPDATE claims SET coverage_status='Declined', status='Declined', updated_at=? WHERE claim_id=?", (ts, cid))
        add_decision(cid, "coverage", "Declined", None, reason); log_audit("coverage_decision", cid, dict(outcome="Declined", reason=reason))
        st.toast("Coverage declined — recorded with reason", icon="🛑")
    else:
        x("UPDATE claims SET status='Correction', updated_at=? WHERE claim_id=?", (ts, cid))
        add_decision(cid, "coverage", "Deferred", None, reason); log_audit("coverage_decision", cid, dict(outcome="Deferred", reason=reason))
        st.toast("Deferred — claim moved to Correction for more information", icon="📨")
    st.rerun()

def override_severity(rec: dict, new_score: float, reason: str) -> None:
    require("override")
    if len(reason.strip()) < 10: st.error("Override reason (≥10 chars) is required."); return
    comp = json.loads(rec["components"]); band = band_of(new_score)
    comp["factors"].append(dict(key="override", label="Manual override", weight=0, factor=0, points=0))
    x("UPDATE claims SET severity=?, band=?, sla_hours=?, components=?, updated_at=? WHERE claim_id=?",
      (new_score, band, SLA[band], json.dumps(comp), iso(now_utc()), rec["claim_id"]))
    add_decision(rec["claim_id"], "severity_override", f"{rec['severity']} → {new_score}", None, reason)
    log_audit("severity_override", rec["claim_id"], dict(old=rec["severity"], new=new_score, reason=reason))
    st.toast(f"Severity overridden → {new_score} ({band})", icon="✍️"); st.rerun()

def save_edit(cid: str, updates: dict) -> None:
    require("edit")
    cur = q("SELECT * FROM claims WHERE claim_id=?", (cid,)).iloc[0].to_dict()
    merged = {**cur, **updates}
    errs, norm = _row_errors(merged)
    if errs:
        st.error("Correction rejected: " + "; ".join(errs)); return
    rec = assess({**cur, **norm}, dup_key_set())
    sets = ",".join(f"{k}=?" for k in COLS if k not in ("claim_id", "created_at"))
    vals = [rec[k] for k in COLS if k not in ("claim_id", "created_at")]
    rec["updated_at"] = iso(now_utc())
    vals[-1] = rec["updated_at"]
    x(f"UPDATE claims SET {sets} WHERE claim_id=?", (*vals, cid))
    log_audit("correction", cid, {k: updates[k] for k in updates})
    st.toast("✏️ Claim corrected, re-validated and re-scored", icon="✏️"); st.rerun()

# ============================================================ live fragments
@st.fragment(run_every=2)
def sidebar_live() -> None:
    ss = st.session_state
    if ss.sim_running and time.monotonic() - ss.last_tick >= ss.sim_interval:
        ss.last_tick = time.monotonic()
        spawn_batch(int(ss.sim_batch))
    df = load_df(); op = df[df["is_open"]]
    rate = int((df["age_h"] < 1 / 60).sum())
    dot = "#34D399" if ss.sim_running else "#FFB020"
    st.markdown(f"""<div class="cs-card"><span class="cs-dot pulse" style="background:{dot};display:inline-block"></span>
<b>{'Live intake' if ss.sim_running else 'Intake paused'}</b>
<div class="cs-mini">Open {len(op)} · Critical {int((op['band'] == 'Critical').sum())} · {rate} claim/min</div>
<div class="cs-mini">{'🎬 Walkthrough ready in Demo Studio' if video_state() == 'ready' else '🎬 Walkthrough rendering…' if video_state() == 'rendering' else ''}</div>
</div>""", unsafe_allow_html=True)

@st.fragment(run_every=2)
def command_center_live() -> None:
    ss = st.session_state
    df = load_df(); op = df[df["is_open"]]
    today = now_utc().date().isoformat()
    intake_today = int((df["created_at"].str[:10] == today).sum())
    settled = df[df["status"] == "Settled"]
    breach = int(op["breached"].sum()); breach_pct = 100 * breach / max(len(op), 1)
    crit_un = int(((op["band"] == "Critical") & (op["adjuster"].isna() | (op["adjuster"] == ""))).sum())
    tiles = [
        dict(label="Open claims", value=len(op), sub=f"+{intake_today} intake today", hue="#2DD4BF"),
        dict(label="Open exposure", value=compact(op["reported_usd"].sum()), sub=f"avg {compact(op['reported_usd'].mean() if len(op) else 0)}", hue="#38BDF8"),
        dict(label="Critical open", value=int((op["band"] == "Critical").sum()), sub=f"{crit_un} unassigned", hue="#FF4D6D"),
        dict(label="Avg completeness", value=f"{op['completeness'].mean() if len(op) else 0:.0f}%", sub=f"{int((op['completeness'] < 80).sum())} need documents", hue="#FBBF24"),
        dict(label="SLA breached", value=breach, sub=f"{breach_pct:.0f}% of open queue", hue="#FB923C"),
        dict(label="Authorized settlements", value=compact(settled["settlement_amount"].sum()), sub=f"{len(settled)} approved by reviewers", hue="#A78BFA"),
    ]
    st.markdown(kpi_html(tiles), unsafe_allow_html=True)
    alerts = []
    if breach: alerts.append(f'<div class="cs-alert a-warn">⏱ {breach} open claims are past their severity SLA — work the Triage Queue top-down.</div>')
    if crit_un: alerts.append(f'<div class="cs-alert a-bad">🚨 {crit_un} Critical claims have no adjuster — use Auto-balance in Triage.</div>')
    if len(op) and op["completeness"].mean() < 75:
        alerts.append('<div class="cs-alert a-info">📄 Completeness is dragging severity up — chase missing documents on high-severity claims.</div>')
    if not alerts: alerts.append('<div class="cs-alert a-ok">✅ Queue healthy — no SLA breaches or unassigned critical claims.</div>')
    st.markdown("".join(alerts), unsafe_allow_html=True)

    with st.container(border=True):
        section("Live intake controls")
        c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
        c1.toggle("▶ Simulation running", key="sim_running")
        c2.toggle("Auto-triage Critical/High", key="sim_autotriage", help="Route severe arrivals straight to In Review")
        if c3.button("🚨 Inject critical claim", width="stretch"): spawn_batch(1, force_critical=True)
        if c4.button("⚡ Burst ×5 arrivals", width="stretch"): spawn_batch(5)
        s1, s2, s3, s4 = st.columns(4)
        s1.slider("New claim every (s)", 2, 20, key="sim_interval")
        s2.slider("Claims per tick", 1, 4, key="sim_batch")
        s3.slider("Severity bias", 0.0, 1.0, key="sim_bias", help="Shifts peril mix and loss sizes upward")
        s4.slider("Anomaly injection", 0.0, 0.4, key="sim_anomaly", help="Probability of breach / late / contradictory data")
        st.caption(f"All controls apply live · engine {RULES_VERSION} · synthetic stream, clearly labeled in lineage.")

    left, right = st.columns([1.15, 1])
    with left:
        section("Live intake feed")
        rows = ss.arrivals[:8]
        if not rows:
            latest = df.sort_values("created_at", ascending=False).head(8)
            rows = [dict(t=dtparse(r.created_at).strftime("%H:%M:%S"), id=r.claim_id, type=r.loss_type,
                         band=r.band, usd=r.reported_usd) for r in latest.itertuples()]
        st.markdown(feed_html(rows), unsafe_allow_html=True)
    with right:
        section("Intake rate · last 60 min")
        recent = df[df["age_h"] <= 1.0].copy()
        buckets = (recent["age_h"] * 60 // 5).astype(int)
        counts = [int((buckets == b).sum()) for b in range(11, -1, -1)]
        fig = go.Figure(go.Scatter(y=counts, mode="lines", fill="tozeroy", line=dict(color="#38BDF8", width=2),
                                   fillcolor="rgba(56,189,248,.18)"))
        fig.update_xaxes(visible=False); fig.update_yaxes(title="claims / 5 min")
        st.plotly_chart(style_fig(fig, 205), width="stretch", key="cc_spark", config={"displayModeBar": False})

    section("Priority spotlight — work these next")
    top = op.sort_values("priority_live", ascending=False).head(3)
    cols = st.columns(3)
    for col, (_, r) in zip(cols, top.iterrows()):
        col.markdown(f"""<div class="cs-card">{badge(r['band'])} <span class="mono">{r['claim_id']}</span>
<div style="margin:6px 0;font-weight:700;">{r['loss_type']} · {compact(r['reported_usd'])}</div>
<div class="cs-mini">priority {r['priority_live']:.0f} · age {r['age_h']:.1f}h / SLA {r['sla_h']:.0f}h
{'· ⚠ breached' if r['breached'] else ''} · {r['adjuster'] or 'Unassigned'}</div>
<div class="cs-mini">→ open Triage Queue or Review &amp; Approvals</div></div>""", unsafe_allow_html=True)

# ============================================================ tab: intake
def tab_intake() -> None:
    section("Documented sample files")
    c1, c2, c3 = st.columns(3)
    valid = sample_valid_df(); bad = sample_bad_df()
    c1.download_button("⬇ sample_valid.csv (10 rows)", valid.to_csv(index=False).encode(), "sample_valid.csv", "text/csv", width="stretch")
    xbuf = io.BytesIO(); valid.to_excel(xbuf, index=False, engine="openpyxl")
    c2.download_button("⬇ sample_valid.xlsx", xbuf.getvalue(), "sample_valid.xlsx",
                       "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", width="stretch")
    c3.download_button("⬇ sample_with_errors.csv (9 rows)", bad.to_csv(index=False).encode(), "sample_with_errors.csv", "text/csv", width="stretch")
    st.caption("Schema: " + ", ".join(REQUIRED_IMPORT) + " (required) + jurisdiction, deductible, policy_limit, estimated_loss, "
               "description, adjuster (optional, drive completeness). Re-importing the same file is blocked by checksum; "
               "duplicate claim_ids are rejected row-by-row and existing records are never overwritten.")

    section("Upload CSV / Excel")
    up = st.file_uploader("Drop a claims file", type=["csv", "xlsx"], key="up_file")
    if up is not None:
        b = up.getvalue()
        try:
            raw = pd.read_excel(io.BytesIO(b), engine="openpyxl") if up.name.lower().endswith(".xlsx") \
                else pd.read_csv(io.BytesIO(b), encoding="utf-8-sig")
        except Exception as e:
            st.error(f"Could not parse '{up.name}': {e}. Export as UTF-8 CSV or a single-sheet XLSX."); raw = None
        if raw is not None:
            ok, errs, preview, fatal = validate_dataframe(raw)
            if fatal:
                st.error("Schema check failed: " + " · ".join(fatal))
            else:
                m1, m2, m3 = st.columns(3)
                m1.markdown(kpi_html([dict(label="Rows", value=len(raw), sub=up.name, hue="#38BDF8")]), unsafe_allow_html=True)
                m2.markdown(kpi_html([dict(label="Valid", value=len(ok), sub="ready to import", hue="#34D399")]), unsafe_allow_html=True)
                m3.markdown(kpi_html([dict(label="Rejected", value=len(errs), sub="actionable errors below", hue="#FF4D6D")]), unsafe_allow_html=True)
                section("Preview (validation applied per row)")
                st.dataframe(preview.head(60), hide_index=True, width="stretch", height=280)
                if not errs.empty:
                    with st.expander(f"❌ {len(errs)} rejected rows — details", expanded=True):
                        st.dataframe(errs, hide_index=True, width="stretch")
                        st.download_button("⬇ Download error report CSV", errs.to_csv(index=False).encode(),
                                           "import_errors.csv", "text/csv",
                                           on_click=log_audit, args=("export", None, "error_report"))
                sha_seen = not q("SELECT batch_id FROM imports WHERE sha256=?", (hashlib.sha256(b).hexdigest(),)).empty
                if sha_seen: st.warning("Checksum match: this file was already imported. Safe re-import strategy blocks duplicates.")
                if st.button(f"📥 Import {len(ok)} valid rows", type="primary", disabled=not ok or not can("import") or sha_seen,
                             help=None if can("import") else "Requires Analyst or Administrator"):
                    try:
                        if commit_import(b, up.name, ok, len(raw), len(errs)): st.rerun()
                    except PermissionError as e: st.error(str(e))

    with st.expander("✍️ Manual claim entry", expanded=False):
        with st.form("manual_form"):
            f1, f2, f3 = st.columns(3)
            cid = f1.text_input("Claim ID (blank = auto)", key="m_id")
            pol = f1.text_input("Policy ID *", value="POL-900001", key="m_pol")
            ins = f2.text_input("Insured *", value=INSUREDS[0], key="m_ins")
            lt = f2.selectbox("Peril *", list(TYPE_CATALOG), key="m_type")
            cur = f3.selectbox("Currency *", list(FX), key="m_cur")
            jur = f3.selectbox("Jurisdiction", JURISDICTIONS, key="m_jur")
            d1, d2 = st.columns(2)
            ld = d1.date_input("Loss date *", value=now_utc().date() - timedelta(days=7), key="m_ld")
            rd = d2.date_input("Reported date *", value=now_utc().date(), key="m_rd")
            n1, n2, n3, n4 = st.columns(4)
            loss = n1.number_input("Reported loss *", min_value=0.0, value=25000.0, step=500.0, key="m_loss")
            est = n2.number_input("Estimated loss", min_value=0.0, value=30000.0, step=500.0, key="m_est")
            ded = n3.number_input("Deductible", min_value=0.0, value=2500.0, step=250.0, key="m_ded")
            lim = n4.number_input("Policy limit", min_value=0.0, value=250000.0, step=5000.0, key="m_lim")
            desc = st.text_area("Description", key="m_desc")
            adj = st.selectbox("Adjuster", ["(unassigned)"] + ADJUSTERS, key="m_adj")
            if st.form_submit_button("Validate & create", type="primary", width="stretch"):
                if not can("manual_create"): st.error("Manual entry requires Analyst or Administrator.")
                else:
                    row = dict(claim_id=cid or None, policy_id=pol, insured_name=ins, loss_type=lt,
                               loss_date=ld.isoformat(), reported_date=rd.isoformat(), jurisdiction=jur,
                               currency=cur, reported_loss=loss, estimated_loss=est or None, deductible=ded,
                               policy_limit=lim or None, description=desc or None,
                               adjuster=None if adj == "(unassigned)" else adj)
                    ok, errs, _, fatal = validate_dataframe(pd.DataFrame([row]))
                    if fatal or not ok:
                        st.error("Rejected: " + ("; ".join(fatal) if fatal else errs.iloc[0]["errors"]))
                    else:
                        rec = prepare_record(ok[0], "manual", dup_keys=dup_key_set())
                        insert_claims([rec]); log_audit("manual_create", rec["claim_id"], rec["band"])
                        st.toast(f"✅ Created {rec['claim_id']} ({rec['band']})", icon="📝"); st.rerun()

    section("Import history (original files preserved with checksums)")
    hist = q("SELECT ts, filename, rows_total, rows_ok, rows_rejected, actor, batch_id, sha256 FROM imports ORDER BY ts DESC")
    if hist.empty: st.caption("No file imports yet — use the sample files above.")
    else: st.dataframe(hist, hide_index=True, width="stretch")

# ============================================================ tab: register
PRESET_VIEWS = {
    "All open claims": dict(rv_status=STATUS_OPEN, rv_bands=BAND_ORDER, rv_sev=0, rv_docs=False, rv_breach=False, rv_arch=False),
    "Critical & High open": dict(rv_status=STATUS_OPEN, rv_bands=["Critical", "High"], rv_sev=0, rv_docs=False, rv_breach=False, rv_arch=False),
    "Missing documents (<80%)": dict(rv_status=STATUS_OPEN, rv_bands=BAND_ORDER, rv_sev=0, rv_docs=True, rv_breach=False, rv_arch=False),
    "SLA breached": dict(rv_status=STATUS_OPEN, rv_bands=BAND_ORDER, rv_sev=0, rv_docs=False, rv_breach=True, rv_arch=False),
    "Ready for settlement": dict(rv_status=["Approved"], rv_bands=BAND_ORDER, rv_sev=0, rv_docs=False, rv_breach=False, rv_arch=False),
}
FILTER_KEYS = ["rv_search", "rv_types", "rv_bands", "rv_status", "rv_sev", "rv_sort", "rv_arch", "rv_docs", "rv_breach"]

def _apply_view() -> None:
    name = st.session_state.rv_pick
    views = {**PRESET_VIEWS, **st.session_state.saved_views}
    if name in views:
        for k, v in views[name].items(): st.session_state[k] = v

def tab_register() -> None:
    ss = st.session_state
    v1, v2, v3 = st.columns([1.2, 1, 0.8])
    v1.selectbox("Saved view", ["— saved views —"] + list(PRESET_VIEWS) + list(ss.saved_views), key="rv_pick", on_change=_apply_view)
    new_name = v2.text_input("Save current filters as", key="rv_newname", placeholder="e.g. My morning queue")
    if v3.button("💾 Save view", width="stretch") and new_name.strip():
        ss.saved_views[new_name.strip()] = {k: ss.get(k) for k in FILTER_KEYS}
        st.toast(f"View '{new_name.strip()}' saved", icon="💾"); st.rerun()

    f1, f2, f3, f4 = st.columns([1.3, 1, 1, 1])
    f1.text_input("🔎 Search id / insured / policy", key="rv_search")
    f2.multiselect("Peril", list(TYPE_CATALOG), key="rv_types")
    f3.multiselect("Band", BAND_ORDER, key="rv_bands")
    f4.multiselect("Status", STATUSES, key="rv_status")
    g1, g2, g3, g4, g5 = st.columns([1, 1.2, 0.8, 0.8, 0.8])
    g1.slider("Min severity", 0, 100, key="rv_sev")
    g2.selectbox("Sort by", ["Priority (live)", "Newest intake", "Reported USD", "Severity", "Completeness ↑"], key="rv_sort")
    g3.checkbox("Incomplete only", key="rv_docs")
    g4.checkbox("Breached only", key="rv_breach")
    g5.checkbox("Include archived", key="rv_arch")

    df = load_df()
    if not ss.rv_arch: df = df[df["status"] != "Archived"]
    if ss.rv_search:
        s = ss.rv_search.lower()
        df = df[df["claim_id"].str.lower().str.contains(s) | df["insured_name"].fillna("").str.lower().str.contains(s)
                | df["policy_id"].fillna("").str.lower().str.contains(s)]
    if ss.rv_types: df = df[df["loss_type"].isin(ss.rv_types)]
    if ss.rv_bands: df = df[df["band"].isin(ss.rv_bands)]
    if ss.rv_status: df = df[df["status"].isin(ss.rv_status)]
    df = df[df["severity"] >= ss.rv_sev]
    if ss.rv_docs: df = df[df["completeness"] < 80]
    if ss.rv_breach: df = df[df["breached"]]
    sort_map = {"Priority (live)": ("priority_live", False), "Newest intake": ("created_at", False),
                "Reported USD": ("reported_usd", False), "Severity": ("severity", False), "Completeness ↑": ("completeness", True)}
    col, asc = sort_map[ss.rv_sort]; df = df.sort_values(col, ascending=asc).reset_index(drop=True)
    st.caption(f"{len(df)} claims match · click rows to select · one row opens the detail drawer")
    if df.empty:
        st.info("No claims match the current filters."); return

    disp = pd.DataFrame({
        "Claim": df["claim_id"], "Band": df["band"].map(lambda b: f"{BAND_EMOJI[b]} {b}"), "Peril": df["loss_type"],
        "Insured": df["insured_name"], "Severity": df["severity"], "Compl. %": df["completeness"],
        "Reported USD": df["reported_usd"], "Status": df["status"], "Age h": df["age_h"].round(1),
        "SLA": [("⚠ " if br else "") + f"{int(s)}h" for br, s in zip(df["breached"], df["sla_h"])],
        "Adjuster": df["adjuster"].fillna("Unassigned"), "Priority": df["priority_live"].round(1)})
    left, right = st.columns([1.35, 1])
    with left:
        sel = st.dataframe(disp, hide_index=True, width="stretch", height=440, key="reg_table",
                           on_select="rerun", selection_mode="multi-row",
                           column_config={"Severity": st.column_config.ProgressColumn(min_value=0, max_value=100, format="%.0f"),
                                          "Compl. %": st.column_config.ProgressColumn(min_value=0, max_value=100, format="%.0f"),
                                          "Reported USD": st.column_config.NumberColumn(format="$%.0f")})
        rows = sel.selection.rows
        if rows:
            ids = disp.iloc[rows]["Claim"].tolist()
            st.markdown(f'<div class="cs-mini">{len(ids)} selected</div>', unsafe_allow_html=True)
            b1, b2, b3, b4 = st.columns(4)
            if b1.button("🚦 To review", disabled=not can("triage"), width="stretch"):
                set_status(ids, "In Review", "send_to_review"); st.rerun()
            if b2.button("📨 Correction", disabled=not can("triage"), width="stretch"):
                set_status(ids, "Correction", "request_correction"); st.rerun()
            if b3.button("🗄️ Archive", disabled=not can("archive"), width="stretch"):
                archive_ids(ids); st.rerun()
            with b4:
                adj = st.selectbox("Assign", ["—"] + ADJUSTERS, key="bulk_adj", label_visibility="collapsed")
            if adj != "—":
                if st.button(f"👤 Assign {len(ids)} → {adj}", disabled=not can("triage")):
                    require("triage")
                    for cid in ids:
                        x("UPDATE claims SET adjuster=?, updated_at=? WHERE claim_id=?", (adj, iso(now_utc()), cid))
                        log_audit("assign", cid, adj)
                    st.toast(f"Assigned {len(ids)} claims to {adj}", icon="👤"); st.rerun()
        if ss.get("undo"):
            if st.button(f"↩ Undo: {ss.undo['label']}"): apply_undo(); st.rerun()
    with right:
        rows = sel.selection.rows
        if len(rows) != 1:
            st.markdown('<div class="cs-card">👈 Select exactly one row to open the claim detail drawer — facts, completeness, '
                        'flags, severity explanation, lineage, decisions and corrections.</div>', unsafe_allow_html=True)
            return
        cid = disp.iloc[rows[0]]["Claim"]
        rec = q("SELECT * FROM claims WHERE claim_id=?", (cid,)).iloc[0].to_dict()
        st.markdown(f'<div class="cs-card"><b class="mono">{cid}</b> &nbsp;{badge(rec["band"])}'
                    f'<span class="cs-chip">{rec["status"]}</span><span class="cs-chip chip-teal">coverage: {rec["coverage_status"]}</span>'
                    + claim_facts_html(rec) + "</div>", unsafe_allow_html=True)
        if rec.get("description"): st.caption("📄 " + rec["description"])
        render_explanation(rec)
        a1, a2 = st.columns(2)
        if a1.button("🚦 Send to review", disabled=not can("triage") or rec["status"] == "In Review", width="stretch"):
            set_status([cid], "In Review", "send_to_review"); st.rerun()
        if a2.button("🗄️ Archive", disabled=not can("archive"), width="stretch"):
            archive_ids([cid]); st.rerun()
        with st.expander("✏️ Correct this claim (re-validates & re-scores)"):
            with st.form(f"edit_{cid}"):
                e1, e2 = st.columns(2)
                nloss = e1.number_input("Reported loss", min_value=0.0, value=float(rec["reported_loss"] or 0), step=500.0)
                nlim = e1.number_input("Policy limit", min_value=0.0, value=float(rec["policy_limit"] or 0), step=5000.0)
                nded = e2.number_input("Deductible", min_value=0.0, value=float(rec["deductible"] or 0), step=250.0)
                nadj = e2.selectbox("Adjuster", ["(unassigned)"] + ADJUSTERS,
                                    index=(ADJUSTERS.index(rec["adjuster"]) + 1) if rec["adjuster"] in ADJUSTERS else 0)
                njur = e1.selectbox("Jurisdiction", JURISDICTIONS,
                                    index=JURISDICTIONS.index(rec["jurisdiction"]) if rec["jurisdiction"] in JURISDICTIONS else 0)
                ndesc = st.text_area("Description", value=rec["description"] or "")
                if st.form_submit_button("Save correction", type="primary", width="stretch", disabled=not can("edit")):
                    save_edit(cid, dict(reported_loss=nloss, policy_limit=nlim or None, deductible=nded,
                                        adjuster=None if nadj == "(unassigned)" else nadj, jurisdiction=njur,
                                        description=ndesc or None))

# ============================================================ tab: triage
def tab_triage() -> None:
    df = load_df(); op = df[df["is_open"]].sort_values("priority_live", ascending=False)
    m1, m2, m3 = st.columns(3)
    m1.markdown(kpi_html([dict(label="Queue size", value=len(op), sub="open claims", hue="#2DD4BF")]), unsafe_allow_html=True)
    m2.markdown(kpi_html([dict(label="SLA breached", value=int(op['breached'].sum()), sub="work these first", hue="#FF4D6D")]), unsafe_allow_html=True)
    m3.markdown(kpi_html([dict(label="Unassigned C/H", value=int((op['band'].isin(['Critical','High']) & (op['adjuster'].isna() | (op['adjuster']==''))).sum()), sub="auto-balance available", hue="#FBBF24")]), unsafe_allow_html=True)
    c1, c2, c3, c4 = st.columns([1.4, 0.8, 1, 1])
    bands = c1.multiselect("Bands", BAND_ORDER, default=BAND_ORDER, key="tq_bands")
    topn = c2.slider("Show top", 5, 60, 20, key="tq_top")
    if c3.button("⚖️ Auto-balance assignments", disabled=not can("triage"), width="stretch"): auto_balance(); st.rerun()
    if c4.button("▶ Work next claim", disabled=not can("triage") or op.empty, width="stretch"):
        nxt = op.iloc[0]["claim_id"]; set_status([nxt], "In Review", "work_next")
        st.toast(f"Now reviewing {nxt} — open Review & Approvals", icon="▶"); st.rerun()
    if st.session_state.get("undo"):
        if st.button(f"↩ Undo: {st.session_state.undo['label']}", key="tq_undo"): apply_undo(); st.rerun()
    queue = op[op["band"].isin(bands)].head(topn).reset_index(drop=True)
    if queue.empty: st.success("Queue is clear for the selected bands. 🎉"); return
    qd = pd.DataFrame({"Claim": queue["claim_id"], "Band": queue["band"].map(lambda b: f"{BAND_EMOJI[b]} {b}"),
                       "Peril": queue["loss_type"], "Priority": queue["priority_live"].round(1),
                       "Severity": queue["severity"], "Age h": queue["age_h"].round(1),
                       "SLA": [("⚠ BREACHED " if br else "") + f"{int(s)}h" for br, s in zip(queue["breached"], queue["sla_h"])],
                       "Compl. %": queue["completeness"], "Reported USD": queue["reported_usd"],
                       "Adjuster": queue["adjuster"].fillna("Unassigned"), "Status": queue["status"]})
    sel = st.dataframe(qd, hide_index=True, width="stretch", height=380, key="tri_table",
                       on_select="rerun", selection_mode="single-row",
                       column_config={"Severity": st.column_config.ProgressColumn(min_value=0, max_value=100, format="%.0f"),
                                      "Compl. %": st.column_config.ProgressColumn(min_value=0, max_value=100, format="%.0f"),
                                      "Reported USD": st.column_config.NumberColumn(format="$%.0f")})
    st.caption("Queue order = severity + aging boost (age/SLA ×10, capped +20). Reordering is done via audited severity override, not drag.")
    left, right = st.columns([1, 1.1])
    with left:
        if sel.selection.rows:
            cid = qd.iloc[sel.selection.rows[0]]["Claim"]
            rec = q("SELECT * FROM claims WHERE claim_id=?", (cid,)).iloc[0].to_dict()
            section(f"Selected · {cid}")
            st.markdown(badge(rec["band"]) + f' <span class="cs-chip">{rec["status"]}</span>', unsafe_allow_html=True)
            st.markdown(claim_facts_html(rec), unsafe_allow_html=True)
            a1, a2 = st.columns(2)
            who = a1.selectbox("Assign to", ["—"] + ADJUSTERS, key="tq_assign")
            if a1.button("👤 Assign", disabled=not can("triage") or who == "—"):
                x("UPDATE claims SET adjuster=?, updated_at=? WHERE claim_id=?", (who, iso(now_utc()), cid))
                log_audit("assign", cid, who); st.toast(f"Assigned to {who}", icon="👤"); st.rerun()
            if a2.button("🚦 Send to review", disabled=not can("triage"), width="stretch"):
                set_status([cid], "In Review", "send_to_review"); st.rerun()
            if a2.button("📨 Needs correction", disabled=not can("triage"), width="stretch"):
                set_status([cid], "Correction", "request_correction"); st.rerun()
        else:
            st.info("Select a queue row to act on it.")
    with right:
        section("Adjuster workload (open claims)")
        wl = op["adjuster"].fillna("Unassigned").value_counts().reset_index()
        wl.columns = ["Adjuster", "Open"]
        fig = go.Figure(go.Bar(orientation="h", y=wl["Adjuster"][::-1], x=wl["Open"][::-1],
                               marker=dict(color=["#FF4D6D" if a == "Unassigned" else "#2DD4BF" for a in wl["Adjuster"]][::-1]),
                               text=wl["Open"][::-1], textposition="outside"))
        st.plotly_chart(style_fig(fig, 320), width="stretch", key="tq_wl", config={"displayModeBar": False})

# ============================================================ tab: analytics
def tab_analytics() -> None:
    include = st.toggle("Include archived/closed in loss totals", value=True, key="an_arch")
    df = load_df()
    base = df if include else df[df["is_open"]]
    op = df[df["is_open"]]
    if base.empty: st.info("No data yet."); return
    wk = base.copy()
    wk["week"] = pd.to_datetime(wk["loss_date"]).dt.to_period("W").dt.start_time
    weekly = wk.groupby("week")[["reported_usd"]].sum().tail(14)
    wow = 0.0
    if len(weekly) >= 2 and weekly["reported_usd"].iloc[-2] > 0:
        wow = 100 * (weekly["reported_usd"].iloc[-1] / weekly["reported_usd"].iloc[-2] - 1)
    worst_type = op.groupby("loss_type")["completeness"].mean().idxmin() if len(op) else "—"
    top_jur = base.groupby("jurisdiction")["reported_usd"].sum().idxmax()
    c1, c2, c3 = st.columns(3)
    c1.markdown(f'<div class="cs-alert a-info">📈 Weekly reported loss {wow:+.0f}% vs prior week — {"rising, watch capacity" if wow > 15 else "within normal band"}.</div>', unsafe_allow_html=True)
    c2.markdown(f'<div class="cs-alert a-warn">📄 Lowest completeness peril: <b>{worst_type}</b> — chase documents to defuse severity.</div>', unsafe_allow_html=True)
    c3.markdown(f'<div class="cs-alert a-bad">📍 Largest exposure jurisdiction: <b>{top_jur}</b> ({compact(base.groupby("jurisdiction")["reported_usd"].sum().max())}).</div>', unsafe_allow_html=True)

    r1a, r1b = st.columns(2)
    with r1a:
        section("Reported loss development · weekly")
        fig = go.Figure()
        fig.add_trace(go.Scatter(x=weekly.index, y=weekly["reported_usd"], name="Reported (USD)",
                                 mode="lines+markers", fill="tozeroy", line=dict(color="#2DD4BF", width=2.5),
                                 fillcolor="rgba(45,212,191,.15)"))
        est = wk.copy(); est["est_usd"] = [usd(v, c) for v, c in zip(est["estimated_loss"].fillna(est["reported_loss"]), est["currency"])]
        we = est.groupby("week")["est_usd"].sum().tail(14)
        fig.add_trace(go.Scatter(x=we.index, y=we.values, name="Estimated (USD)", mode="lines",
                                 line=dict(color="#A78BFA", width=2, dash="dash")))
        st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_trend", config={"displayModeBar": False})
    with r1b:
        section("Exposure by peril")
        bt = base.groupby("loss_type")["reported_usd"].sum().sort_values()
        fig = go.Figure(go.Bar(orientation="h", y=bt.index, x=bt.values,
                               marker=dict(color=[TYPE_CATALOG[t]["hue"] for t in bt.index]),
                               text=[compact(v) for v in bt.values], textposition="outside"))
        st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_type", config={"displayModeBar": False})
    r2a, r2b = st.columns(2)
    with r2a:
        section("Open queue · severity bands")
        bc = op["band"].value_counts().reindex(BAND_ORDER).fillna(0)
        fig = go.Figure(go.Pie(labels=BAND_ORDER, values=bc.values, hole=0.62,
                               marker=dict(colors=[BAND_COLORS[b] for b in BAND_ORDER]),
                               textinfo="label+value", textfont=dict(size=12)))
        fig.add_annotation(text=f"<b>{len(op)}</b><br>open", showarrow=False, font=dict(size=18, color="#E8F1F8"))
        st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_bands", config={"displayModeBar": False})
    with r2b:
        section("Completeness vs severity · chase the bottom-right")
        fig = go.Figure()
        for b in BAND_ORDER:
            sub = op[op["band"] == b]
            if sub.empty: continue
            fig.add_trace(go.Scatter(x=sub["completeness"], y=sub["severity"], mode="markers", name=b,
                                     marker=dict(color=BAND_COLORS[b], size=(np.sqrt(sub["reported_usd"]) / 14 + 6).clip(6, 32),
                                                 line=dict(width=1, color="rgba(255,255,255,.35)")),
                                     customdata=sub[["claim_id", "loss_type", "reported_usd"]],
                                     hovertemplate="%{customdata[0]} · %{customdata[1]}<br>%{customdata[2]:$,.0f}<br>compl %{x}% · sev %{y}<extra></extra>"))
        fig.add_vline(x=60, line_dash="dot", line_color="rgba(255,176,32,.5)")
        fig.add_hline(y=60, line_dash="dot", line_color="rgba(255,77,109,.5)")
        fig.update_xaxes(title="Completeness %"); fig.update_yaxes(title="Severity")
        st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_scatter", config={"displayModeBar": False})
    r3a, r3b = st.columns(2)
    with r3a:
        section("SLA compliance by band (open)")
        within = [int(((op["band"] == b) & ~op["breached"]).sum()) for b in BAND_ORDER]
        breached = [int(((op["band"] == b) & op["breached"]).sum()) for b in BAND_ORDER]
        fig = go.Figure([go.Bar(name="Within SLA", x=BAND_ORDER, y=within, marker_color="#34D399"),
                         go.Bar(name="Breached", x=BAND_ORDER, y=breached, marker_color="#FF4D6D")])
        fig.update_layout(barmode="stack")
        st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_sla", config={"displayModeBar": False})
    with r3b:
        section("Data-quality flag frequency (open)")
        all_flags: list[str] = []
        for s in op["flags"]: all_flags += json.loads(s or "[]")
        if all_flags:
            fc = pd.Series(all_flags).value_counts()
            cum = 100 * fc.cumsum() / fc.sum()
            fig = go.Figure([go.Bar(x=[FLAG_LABELS.get(f, f) for f in fc.index], y=fc.values, marker_color="#FBBF24", name="Count"),
                             go.Scatter(x=[FLAG_LABELS.get(f, f) for f in fc.index], y=cum.values, name="Cumulative %",
                                        yaxis="y2", line=dict(color="#38BDF8", width=2))])
            fig.update_layout(yaxis2=dict(overlaying="y", side="right", range=[0, 100], showgrid=False, title="%"))
            fig.update_xaxes(tickangle=-20)
            st.plotly_chart(style_fig(fig, 300), width="stretch", key="an_flags", config={"displayModeBar": False})
        else:
            st.success("No data-quality flags on open claims.")
    st.download_button("⬇ Download analytics dataset (CSV)",
                       base[["claim_id", "loss_type", "band", "severity", "completeness", "reported_usd",
                             "status", "jurisdiction", "age_h", "breached"]].to_csv(index=False).encode(),
                       "claims_analytics.csv", "text/csv", on_click=log_audit, args=("export", None, "analytics_dataset"))

# ============================================================ tab: review
def tab_review() -> None:
    if not can("review_decide"):
        st.markdown('<div class="cs-lock">🔒 Coverage and settlement decisions are reserved for <b>Senior Reviewer</b> and '
                    '<b>Administrator</b>. You can inspect the queue and every explanation below — switch role in the sidebar '
                    'to exercise the authorized path. All decisions require a reason and are audited.</div>', unsafe_allow_html=True)
    df = load_df()
    pend = df[df["status"].eq("In Review") | (df["is_open"] & df["band"].isin(["Critical", "High"]))] \
        .sort_values("priority_live", ascending=False)
    if pend.empty: st.success("Nothing awaiting review. Inject claims from the Command Center to exercise this flow."); return
    opts = pend["claim_id"].tolist()
    labels = {r.claim_id: f"{r.claim_id} · {BAND_EMOJI[r.band]} {r.band} · {compact(r.reported_usd)} · {r.loss_type}"
              for r in pend.itertuples()}
    pick = st.selectbox("Review queue (priority order)", opts, format_func=lambda c: labels[c], key="rvw_pick")
    rec = q("SELECT * FROM claims WHERE claim_id=?", (pick,)).iloc[0].to_dict()
    left, right = st.columns([1, 1.15])
    with left:
        st.markdown(f'<div class="cs-card"><b class="mono">{pick}</b> &nbsp;{badge(rec["band"])}'
                    f'<span class="cs-chip">{rec["status"]}</span>' + claim_facts_html(rec) + "</div>", unsafe_allow_html=True)
        if rec.get("description"): st.caption("📄 " + rec["description"])
        render_explanation(rec)
        with st.expander("✍️ Manual severity override (audited)"):
            ns = st.slider("New severity", 0.0, 100.0, float(rec["severity"]), 0.5, key="ov_score")
            rr = st.text_area("Override reason (required)", key="ov_reason")
            if st.button("Apply override", disabled=not can("override"),
                         help=None if can("override") else "Requires Senior Reviewer or Administrator"):
                try: override_severity(rec, ns, rr)
                except PermissionError as e: st.error(str(e))
    with right:
        section("Authorized decision")
        cap = max(0.0, float(rec.get("policy_limit") or TYPE_CATALOG[rec["loss_type"]]["ref_limit"]) - float(rec.get("deductible") or 0))
        st.caption(f"Maximum authorizable settlement: {money(cap)} {rec['currency']} "
                   f"({'policy limit' if rec.get('policy_limit') else 'catalog reference limit'} net of deductible).")
        with st.form(f"decision_{pick}"):
            outcome = st.radio("Coverage decision", ["Approve coverage", "Decline coverage", "Defer — request information"], key=f"dc_{pick}")
            settle = st.checkbox(f"Authorize settlement now (≤ {money(cap)} {rec['currency']})", key=f"st_{pick}",
                                 disabled=not can("settle"))
            amount = st.number_input("Settlement amount", min_value=0.0, max_value=float(cap) if cap > 0 else 1.0,
                                     value=float(round(cap * 0.8, 2)), step=100.0, key=f"amt_{pick}")
            reason = st.text_area("Decision reason (required, ≥10 chars — preserved in audit)", key=f"rsn_{pick}")
            ok = st.form_submit_button("🖋 Record decision", type="primary", width="stretch", disabled=not can("review_decide"))
        if ok:
            try:
                if settle and outcome != "Approve coverage": st.error("Settlement can only be authorized alongside coverage approval.")
                else: submit_decision(rec, outcome, settle, amount, reason)
            except PermissionError as e: st.error(str(e))
        section("Recent decisions (all claims)")
        d = q("""SELECT d.ts, d.claim_id, d.kind, d.outcome, d.amount, d.actor, d.role
                 FROM decisions d ORDER BY d.ts DESC LIMIT 15""")
        st.dataframe(d, hide_index=True, width="stretch", height=300)

# ============================================================ tab: reports & audit
def md_table(headers: list[str], rows: list[list]) -> str:
    out = "| " + " | ".join(headers) + " |\n|" + "|".join(["---"] * len(headers)) + "|\n"
    return out + "\n".join("| " + " | ".join(str(c) for c in r) + " |" for r in rows)

def build_summary(df: pd.DataFrame, scope: str) -> str:
    op = df[df["is_open"]]
    bc = op["band"].value_counts().reindex(BAND_ORDER).fillna(0).astype(int)
    bt = df.groupby("loss_type")["reported_usd"].sum().sort_values(ascending=False)
    top = op.sort_values("priority_live", ascending=False).head(5)
    dec = q("SELECT ts, claim_id, kind, outcome, actor, role FROM decisions ORDER BY ts DESC LIMIT 8")
    return f"""# {APP_NAME} — Shift Summary Report
**Generated:** {iso(now_utc())} · **Scope:** {scope} · **Prepared by:** {ROLE_USER[st.session_state.role]} ({st.session_state.role})
**Engine:** {RULES_VERSION} · **Reference data:** {FX_VERSION} · **Schema:** {SCHEMA_VERSION} · **Data:** SYNTHETIC demonstration records

## Portfolio
- Open claims: **{len(op)}** · Open exposure: **USD {op['reported_usd'].sum():,.0f}**
- SLA breached: **{int(op['breached'].sum())}** ({100 * op['breached'].sum() / max(len(op), 1):.0f}% of open)
- Average completeness: **{op['completeness'].mean() if len(op) else 0:.0f}%**

## Open severity bands
{md_table(["Band", "Count"], [[b, int(bc[b])] for b in BAND_ORDER])}

## Exposure by peril (USD, FX-normalized)
{md_table(["Peril", "Reported USD"], [[t, f"{v:,.0f}"] for t, v in bt.items()])}

## Top 5 priorities
{md_table(["Claim", "Band", "Peril", "Priority", "Reported USD"], [[r.claim_id, r.band, r.loss_type, f"{r.priority_live:.0f}", f"{r.reported_usd:,.0f}"] for r in top.itertuples()])}

## Latest authorized decisions
{md_table(["When", "Claim", "Kind", "Outcome", "Actor", "Role"], dec.values.tolist()) if not dec.empty else "_No decisions recorded yet._"}

---
*Decision-support output on synthetic data. Coverage and settlement decisions require authorized human approval.
Not regulated financial advice. Every figure is traceable via claim lineage and the audit log.*
"""

def tab_reports() -> None:
    section("Report builder")
    df = load_df()
    scopes = {"All open claims": df[df["is_open"]], "Critical & High (open)": df[df["is_open"] & df["band"].isin(["Critical", "High"])],
              "SLA breached (open)": df[df["breached"]], "Settled & approved": df[df["status"].isin(["Settled", "Approved"])],
              "Everything (incl. archived)": df}
    c1, c2 = st.columns(2)
    scope = c1.selectbox("Scope", list(scopes), key="rep_scope")
    fmts = ["Markdown executive summary", "Aggregate CSV (no PII)"] + (["Claims CSV (records)", "JSON snapshot"] if can("export_raw") else [])
    fmt = c2.selectbox("Format", fmts, key="rep_format")
    sub = scopes[scope]
    if fmt == "Markdown executive summary":
        md = build_summary(sub, scope); data, fname, mime = md.encode(), "claimsight_summary.md", "text/markdown"
        with st.expander("Preview report", expanded=True): st.markdown(md)
    elif fmt == "Aggregate CSV (no PII)":
        agg = sub.groupby(["loss_type", "band"]).agg(claims=("claim_id", "count"), reported_usd=("reported_usd", "sum"),
                                                     avg_severity=("severity", "mean"), avg_completeness=("completeness", "mean")).reset_index()
        data, fname, mime = agg.to_csv(index=False).encode(), "claims_aggregate.csv", "text/csv"
        st.dataframe(agg, hide_index=True, width="stretch", height=260)
    elif fmt == "Claims CSV (records)":
        data, fname, mime = sub.to_csv(index=False).encode(), "claims_records.csv", "text/csv"
        st.dataframe(sub[["claim_id", "loss_type", "band", "severity", "reported_usd", "status"]].head(30), hide_index=True, width="stretch")
    else:
        snap = dict(meta=dict(app=APP_NAME, rules=RULES_VERSION, fx=FX_VERSION, schema=SCHEMA_VERSION,
                              generated=iso(now_utc()), synthetic=True),
                    claims=json.loads(sub.to_json(orient="records")),
                    decisions=json.loads(q("SELECT * FROM decisions").to_json(orient="records")))
        data, fname, mime = json.dumps(snap, indent=2).encode(), "claimsight_snapshot.json", "application/json"
        st.code(json.dumps(snap["meta"], indent=2))
    st.download_button(f"⬇ Download {fmt}", data, fname, mime, type="primary",
                       on_click=log_audit, args=("export", None, dict(format=fmt, scope=scope, rows=len(sub))))

    section("Audit log")
    adf = q("SELECT ts, actor, role, action, claim_id, details FROM audit ORDER BY id DESC LIMIT 2000")
    a1, a2 = st.columns([1.4, 1])
    actions = a1.multiselect("Filter actions", sorted(adf["action"].unique().tolist()), key="au_actions")
    search = a2.text_input("Search claim / actor", key="au_search")
    view = adf[adf["action"].isin(actions)] if actions else adf
    if search:
        s = search.lower()
        view = view[view["claim_id"].fillna("").str.lower().str.contains(s) | view["actor"].str.lower().str.contains(s)]
    st.dataframe(view.head(400), hide_index=True, width="stretch", height=300)
    st.download_button("⬇ Export audit CSV", view.to_csv(index=False).encode(), "audit_log.csv", "text/csv",
                       on_click=log_audit, args=("export", None, "audit_log"))

    with st.expander("🛡️ Role & permission matrix"):
        mx = pd.DataFrame({r: ["✅" if a in PERMS[r] else "—" for a in ALL_PERMS] for r in ROLES}, index=ALL_PERMS)
        st.dataframe(mx, width="stretch")
        st.caption("Authorization is enforced in the service layer (require()), not only by hiding buttons. "
                   "Coverage/settlement/override are reserved for Senior Reviewer and Administrator.")
    with st.expander("📚 Data dictionary"):
        dd = [
            ("claim_id", "TEXT PK", "—", "Stable claim identifier", "unique", "public"),
            ("policy_id", "TEXT", "—", "Policy reference", "required", "internal"),
            ("insured_name", "TEXT", "—", "Insured organization (synthetic)", "required", "PII-like"),
            ("loss_type", "ENUM", "—", "Peril from reference catalog", "8 perils", "internal"),
            ("loss_date / reported_date", "DATE ISO", "UTC date", "Event vs intake dates", "reported ≥ loss; loss ≤ today", "internal"),
            ("currency", "ENUM", "ISO 4217", "Native amount currency", "USD/EUR/GBP/CAD", "internal"),
            ("reported_loss", "REAL", "currency", "Claimant-reported amount", "> 0", "confidential"),
            ("estimated_loss / deductible / policy_limit", "REAL", "currency", "Reserve estimate / friction / cap", "≥ 0", "confidential"),
            ("severity", "REAL", "0–100", "Deterministic weighted score", "engine " + RULES_VERSION, "internal"),
            ("band", "ENUM", "—", "Severity band", "Critical/High/Medium/Low", "internal"),
            ("completeness", "REAL", "%", "Filled required operational fields / 13", "0–100", "internal"),
            ("flags / missing_fields / components", "JSON", "—", "Anomalies, gaps, score explanation", "versioned", "internal"),
            ("status / coverage_status", "ENUM", "—", "Lifecycle / coverage gate", "8 statuses / Pending-Approved-Declined", "internal"),
            ("settlement_amount", "REAL", "currency", "Authorized settlement", "≤ limit − deductible", "restricted"),
            ("source / batch_id", "TEXT", "—", "Lineage: seed/sim/import/manual + file batch", "checksum in imports", "internal"),
            ("schema_version / rules_version", "TEXT", "—", "Transformation provenance", "pinned per record", "internal"),
            ("created_at / updated_at", "TS ISO", "UTC", "Record timestamps", "monotonic updates", "internal"),
        ]
        st.dataframe(pd.DataFrame(dd, columns=["Field", "Type", "Unit", "Meaning", "Validation", "Sensitivity"]),
                     hide_index=True, width="stretch")
    with st.expander("🧬 Lineage, versions & worked example"):
        st.markdown(f"""**Lineage chain:** source file (SHA-256 preserved in `source_files/`) → import batch → claim row →
deterministic engine **{RULES_VERSION}** (FX **{FX_VERSION}**, schema **{SCHEMA_VERSION}**) → explanation JSON →
authorized decision → audit event. Simulation and seed records are labeled `simulation` / `demo_seed`.

**Worked example (hand-checkable):** reported 250,000 USD, limit 500,000, General Liability, 10-day delay,
missing description + adjuster (completeness 84.6%), no flags:""")
        t = now_utc().date()
        fixed = dict(claim_id="FIXTURE-1", policy_id="POL-FIX", insured_name="Fixture Co", loss_type="General Liability",
                     loss_date=(t - timedelta(days=40)).isoformat(), reported_date=(t - timedelta(days=30)).isoformat(),
                     jurisdiction="NY", currency="USD", reported_loss=250000.0, estimated_loss=300000.0, deductible=5000.0,
                     policy_limit=500000.0, description=None, adjuster=None)
        fx = assess(dict(fixed))
        st.dataframe(pd.DataFrame(json.loads(fx["components"])["factors"])[["label", "weight", "factor", "points"]],
                     hide_index=True, width="stretch")
        st.caption(f"Sum = {fx['severity']} → band {fx['band']}. This fixture is asserted by the integrity checks below.")
    with st.expander("💾 Retention, backup & restore"):
        r1, r2 = st.columns(2)
        days = r1.slider("Purge archived older than (days)", 7, 365, 90, key="ret_days")
        cutoff = iso(now_utc() - timedelta(days=days))
        n_old = int(q("SELECT COUNT(*) n FROM claims WHERE status='Archived' AND updated_at<?", (cutoff,))["n"][0])
        r1.caption(f"{n_old} archived records eligible.")
        if r1.button("🧹 Purge eligible archived", disabled=not can("purge") or n_old == 0):
            x("DELETE FROM claims WHERE status='Archived' AND updated_at<?", (cutoff,))
            log_audit("purge", None, dict(days=days, removed=n_old)); st.toast(f"Purged {n_old} archived records", icon="🧹"); st.rerun()
        if r2.button("📦 Create backup now", disabled=not can("backup"), width="stretch"):
            dest = BKP_DIR / f"claimsight_{now_utc():%Y%m%d_%H%M%S}.db"
            with closing(db()) as c: c.execute("PRAGMA wal_checkpoint(FULL)")
            shutil.copy2(DB_PATH, dest); log_audit("backup", None, dest.name)
            st.toast(f"Backup created: {dest.name}", icon="📦"); st.rerun()
        bkps = sorted(BKP_DIR.glob("*.db"), reverse=True)
        if bkps:
            pick = r2.selectbox("Download a backup", [b.name for b in bkps], key="bk_pick")
            r2.download_button("⬇ Download backup file", (BKP_DIR / pick).read_bytes(), pick, "application/octet-stream",
                               on_click=log_audit, args=("export", None, f"backup:{pick}"))
        st.code("# Restore (PowerShell): stop the app first (Ctrl+C), then:\n"
                "Copy-Item .\\claimsight_data\\backups\\<backup>.db .\\claimsight_data\\claimsight.db -Force\n"
                "streamlit run app.py   # restart and verify record counts", language="powershell")
        st.caption("PostgreSQL migration path: schema is fully relational with stable keys; swap the db() helper for a "
                   "SQLAlchemy engine, keep WAL-equivalent transactionality, and move source files to object storage.")
    with st.expander("🧪 Integrity checks (software correctness — runnable test suite)"):
        if st.button("▶ Run integrity checks", type="primary"):
            results = run_self_checks()
            rdf = pd.DataFrame(results)
            passed = int((rdf["Result"] == "✅").sum())
            st.markdown(kpi_html([dict(label="Checks passed", value=f"{passed}/{len(rdf)}",
                                       sub="domain validity still requires practitioner sign-off",
                                       hue="#34D399" if passed == len(rdf) else "#FF4D6D")]), unsafe_allow_html=True)
            st.dataframe(rdf, hide_index=True, width="stretch")
            log_audit("self_check", None, dict(passed=passed, total=len(rdf)))
    with st.expander("☢️ Danger zone — reset demo (Administrator)"):
        confirm = st.checkbox("I understand this wipes claims, decisions, audit and imports, then re-seeds.", key="reset_confirm")
        if st.button("♻️ Reset & re-seed demo", disabled=not can("reset") or not confirm):
            for t_ in ("claims", "decisions", "audit", "imports"): x(f"DELETE FROM {t_}")
            seed_if_empty()
            st.session_state.arrivals = []; st.session_state.undo = None; st.session_state.last_tick = time.monotonic()
            log_audit("demo_reset", None, "re-seeded")
            st.toast("Demo reset & re-seeded from a clean database", icon="♻️"); st.rerun()

# ============================================================ integrity checks
def run_self_checks() -> list[dict]:
    res: list[dict] = []
    def add(name: str, ok: bool, detail: str) -> None:
        res.append(dict(Check=name, Result="✅" if ok else "❌", Details=detail))
    df = q("SELECT * FROM claims")
    add("Severity & completeness bounds", bool(df["severity"].between(0, 100).all() and df["completeness"].between(0, 100).all()),
        f"{len(df)} records within [0,100]")
    non_ov = df[~df["components"].str.contains('"override"', na=False)]
    add("Band mapping consistent with score", bool((non_ov["band"] == non_ov["severity"].map(band_of)).all()),
        f"{len(non_ov)} non-overridden records checked")
    add("Claim IDs unique", bool(df["claim_id"].is_unique), f"{df['claim_id'].nunique()} unique keys")
    add("Currencies within reference catalog", bool(df["currency"].isin(FX).all()), ", ".join(sorted(df["currency"].unique())))
    sample = non_ov.sample(min(30, len(non_ov)), random_state=SEED)
    ok_re = True
    for r in sample.itertuples():
        a = assess(r._asdict() if hasattr(r, "_asdict") else dict(r))
        if abs(a["severity"] - r.severity) > 0.15 or abs(a["completeness"] - r.completeness) > 0.15: ok_re = False
    add("Engine recomputation matches stored scores", ok_re, f"{len(sample)} sampled records, tolerance ±0.15")
    settled = df[df["status"] == "Settled"]
    ok_set = True
    for r in settled.itertuples():
        cap = max(0.0, float(r.policy_limit or TYPE_CATALOG[r.loss_type]["ref_limit"]) - float(r.deductible or 0))
        if r.coverage_status != "Approved" or not (0 < (r.settlement_amount or 0) <= cap + 1e-6): ok_set = False
    add("Settlements ≤ limit − deductible & coverage approved", ok_set, f"{len(settled)} settled records checked")
    dec = q("SELECT * FROM decisions")
    aud = q("SELECT action, claim_id FROM audit")
    amap = {"coverage": "coverage_decision", "settlement": "settlement", "severity_override": "severity_override"}
    pairs = set(zip(aud["action"], aud["claim_id"]))
    ok_aud = all((amap.get(r.kind), r.claim_id) in pairs for r in dec.itertuples())
    add("Every decision has a matching audit event", ok_aud, f"{len(dec)} decisions traced")
    t = now_utc().date()
    fixed = dict(claim_id="FIXTURE-1", policy_id="POL-FIX", insured_name="Fixture Co", loss_type="General Liability",
                 loss_date=(t - timedelta(days=40)).isoformat(), reported_date=(t - timedelta(days=30)).isoformat(),
                 jurisdiction="NY", currency="USD", reported_loss=250000.0, estimated_loss=300000.0,
                 deductible=5000.0, policy_limit=500000.0, description=None, adjuster=None)
    a1, a2 = assess(dict(fixed)), assess(dict(fixed))
    add("Regression fixture deterministic", a1["components"] == a2["components"] and a1["severity"] == a2["severity"],
        f"fixture severity {a1['severity']} ({a1['band']})")
    ok_v, errs_v, _, fatal_v = validate_dataframe(sample_valid_df(), check_db=False)
    ok_b, errs_b, _, fatal_b = validate_dataframe(sample_bad_df(), check_db=False)
    add("Validator accepts documented valid sample", not fatal_v and len(ok_v) == 10, f"{len(ok_v)}/10 rows accepted")
    add("Validator rejects malformed sample with actionable errors", not fatal_b and len(errs_b) >= 8,
        f"{len(errs_b)} rows rejected with row-level messages")
    integ = q("PRAGMA integrity_check")
    add("SQLite integrity_check", str(integ.iloc[0, 0]) == "ok", str(integ.iloc[0, 0]))
    return res

# ============================================================ demo video (auto-generated MP4)
_VIDEO_LOCK = threading.Lock()
_VIDEO_STATE = {"state": "idle", "msg": ""}

def video_state() -> str:
    with _VIDEO_LOCK:
        if _VIDEO_STATE["state"] == "rendering": return "rendering"
    return "ready" if VIDEO_PATH.exists() else "idle"

def stats_snapshot() -> dict:
    df = load_df(); op = df[df["is_open"]]
    feed = df.sort_values("created_at", ascending=False).head(6)
    wk = df.copy(); wk["week"] = pd.to_datetime(wk["loss_date"]).dt.to_period("W").dt.start_time
    weekly = wk.groupby("week")["reported_usd"].sum().tail(10)
    top = op.sort_values("priority_live", ascending=False).head(5)
    return dict(
        open=int(len(op)), exposure=float(op["reported_usd"].sum()),
        critical=int((op["band"] == "Critical").sum()),
        completeness=float(op["completeness"].mean() if len(op) else 0),
        breach_pct=float(100 * op["breached"].sum() / max(len(op), 1)),
        settled=float(df[df["status"] == "Settled"]["settlement_amount"].sum()),
        bands={b: int((op["band"] == b).sum()) for b in BAND_ORDER},
        feed=[dict(id=r.claim_id, type=r.loss_type, band=r.band, usd=float(r.reported_usd)) for r in feed.itertuples()],
        queue=[dict(id=r.claim_id, band=r.band, type=r.loss_type, pr=float(r.priority_live)) for r in top.itertuples()],
        weeks=[d.strftime("%b %d") for d in weekly.index], reported=[float(v) for v in weekly.values])

def render_demo_video(stats: dict, seconds: float = 14, fps: int = 12, size: tuple = (848, 480),
                      progress=None) -> dict:
    import matplotlib
    matplotlib.use("Agg", force=True)
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyBboxPatch, Circle, Wedge, Rectangle
    import imageio
    plt.rcParams["font.family"] = "DejaVu Sans"
    W, H = size
    fig = plt.figure(figsize=(W / 100, H / 100), dpi=100)
    ax = fig.add_axes([0, 0, 1, 1]); ax.set_xlim(0, 100); ax.set_ylim(0, 100); ax.axis("off")
    gx = np.linspace(0, 1, 160); gy = np.linspace(0, 1, 90); X, Y = np.meshgrid(gx, gy)
    def blob(cx, cy, s): return np.exp(-((X - cx) ** 2 + (Y - cy) ** 2) / s)
    bg = np.zeros((90, 160, 3)) + np.array([7, 13, 26]) / 255
    bg += blob(.15, .85, .08)[..., None] * np.array([45, 212, 191]) / 255 * .22
    bg += blob(.9, .2, .12)[..., None] * np.array([167, 139, 250]) / 255 * .16
    bg += blob(.6, .9, .2)[..., None] * np.array([56, 189, 248]) / 255 * .10
    bg = np.clip(bg, 0, 1)
    BC = {"Critical": "#FF4D6D", "High": "#FFB020", "Medium": "#38BDF8", "Low": "#34D399"}
    def T(x, y, s, sz=10, c="#E8F1F8", w="normal", a=1, ha="left", mono=False):
        ax.text(x, y, s, fontsize=sz, color=c, fontweight=w, alpha=max(0, min(1, a)), ha=ha, va="center",
                family="DejaVu Sans Mono" if mono else "DejaVu Sans", zorder=5)
    def card(x, y, w, h, fc="#101E33", ec="#2DD4BF", a=1, ea=.35):
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.3,rounding_size=1.2",
                                    fc=fc, ec=ec, alpha=a, lw=1, zorder=3))
        ax.add_patch(FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.3,rounding_size=1.2",
                                    fc="none", ec=ec, alpha=a * ea, lw=1, zorder=4))
    def base(t):
        ax.clear(); ax.set_xlim(0, 100); ax.set_ylim(0, 100); ax.axis("off")
        ax.imshow(bg, extent=(0, 100, 0, 100), aspect="auto", zorder=0, interpolation="bilinear")
        ax.add_patch(Circle((20 + 8 * math.sin(t / 3), 80), 18, fc="#2DD4BF", alpha=.04, zorder=1))
        ax.add_patch(Circle((85 + 6 * math.cos(t / 4), 25), 22, fc="#A78BFA", alpha=.04, zorder=1))
        T(3, 96, "ClaimSight ● LIVE DEMO", 8, "#5EEAD4", "bold")
        T(97, 96, "SYNTHETIC DATA", 7, "#FFCF7D", "bold", ha="right")
    total = int(seconds * fps)
    weights = [0.16, 0.26, 0.22, 0.24, 0.12]
    bounds = np.cumsum([0] + weights)
    tmp = VIDEO_DIR / f"_tmp_{uuid.uuid4().hex[:6]}.mp4"
    writer = imageio.get_writer(str(tmp), fps=fps, codec="libx264", quality=7, pixelformat="yuv420p", macro_block_size=1)
    try:
        for f in range(total):
            t = f / fps; u = f / total
            scene = int(np.searchsorted(bounds, u, side="right") - 1); scene = min(scene, 4)
            p = (u - bounds[scene]) / (bounds[scene + 1] - bounds[scene]); e = ease(p)
            base(t)
            if scene == 0:
                T(50, 60, "ClaimSight", 34, "#5EEAD4", "bold", e, ha="center")
                T(50, 48, "Insurance Claims Triage & Loss Analytics Workbench", 11, "#C9D6E3", a=ease(p * 1.4 - .2), ha="center")
                ax.add_patch(Rectangle((50 - 30 * e, 41), 60 * e, .7, fc="#38BDF8", alpha=.9, zorder=5))
                T(50, 32, "Auto-generated walkthrough of the live synthetic demo", 9, "#8FA6BC", a=ease(p * 1.6 - .5), ha="center")
                T(50, 24, "Human-in-the-loop · Audited · Export-ready", 9, "#A78BFA", "bold", ease(p * 1.8 - .8), ha="center")
            elif scene == 1:
                T(4, 88, "LIVE CLAIM INTAKE", 15, "#E8F1F8", "bold")
                kpis = [("OPEN CLAIMS", stats["open"], "#2DD4BF"), ("OPEN EXPOSURE", stats["exposure"], "#38BDF8"),
                        ("CRITICAL", stats["critical"], "#FF4D6D"), ("COMPLETENESS %", stats["completeness"], "#FBBF24")]
                for i, (lab, val, hue) in enumerate(kpis):
                    x = 4 + (i % 2) * 23; y = 58 - (i // 2) * 26
                    card(x, y, 21, 22, ec=hue, a=e)
                    T(x + 1.5, y + 17, lab, 6.5, "#8FA6BC", "bold", e)
                    vv = val * e
                    txt = compact(vv) if lab == "OPEN EXPOSURE" else f"{vv:.0f}"
                    T(x + 1.5, y + 9, txt, 17, "#F2F8FD", "bold", e)
                T(53, 84, "Incoming claims stream", 10, "#5EEAD4", "bold", e)
                for i, r in enumerate(stats["feed"][:6]):
                    pa = ease((p - i / 8) * 4); 
                    if pa <= 0: continue
                    y = 74 - i * 10; xo = (1 - pa) * 6
                    card(52 + xo, y - 3.4, 44, 7.6, ec=BC[r["band"]], a=pa, ea=.5)
                    ax.add_patch(Circle((54.5 + xo, y), 1.1, fc=BC[r["band"]], alpha=pa, zorder=5))
                    T(57 + xo, y, r["id"], 6.6, "#9FB6CC", mono=True, a=pa)
                    T(72 + xo, y, r["type"][:16], 6.6, "#C9D6E3", a=pa)
                    T(94.5 + xo, y, compact(r["usd"]), 7, "#E8F1F8", "bold", pa, ha="right")
            elif scene == 2:
                T(4, 88, "SEVERITY & TRIAGE", 15, "#E8F1F8", "bold")
                mx = max(max(stats["bands"].values()), 1)
                for i, b in enumerate(["Critical", "High", "Medium", "Low"]):
                    y = 72 - i * 14; v = stats["bands"][b]
                    T(5, y + 4.5, b.upper(), 7.5, BC[b], "bold", e)
                    ax.add_patch(Rectangle((5, y - 2), 38, 4.5, fc="#0E1B2E", alpha=e, zorder=3))
                    ax.add_patch(Rectangle((5, y - 2), 38 * (v / mx) * e, 4.5, fc=BC[b], alpha=.9 * e, zorder=4))
                    T(5 + 38 * (v / mx) * e + 1.5, y, str(v), 9, "#E8F1F8", "bold", e)
                T(53, 84, "Priority queue — work top-down", 10, "#5EEAD4", "bold", e)
                for i, r in enumerate(stats["queue"][:5]):
                    pa = ease((p - i / 7) * 4)
                    if pa <= 0: continue
                    y = 74 - i * 11
                    card(52, y - 4, 44, 8.6, ec=BC[r["band"]], a=pa, ea=.5)
                    T(54, y, f"#{i+1}", 8, "#8FA6BC", "bold", pa)
                    T(59, y, r["id"], 6.6, "#9FB6CC", mono=True, a=pa)
                    T(74, y, r["type"][:14], 6.6, "#C9D6E3", a=pa)
                    T(94.5, y, f"{r['pr']:.0f}", 9, BC[r["band"]], "bold", pa, ha="right")
                T(5, 12, f"SLA breached: {stats['breach_pct']:.0f}% of open queue", 8, "#FFCF7D", a=e)
            elif scene == 3:
                T(4, 88, "LOSS ANALYTICS", 15, "#E8F1F8", "bold")
                vals = stats["reported"] or [0, 0]; n = max(2, int(len(vals) * e))
                xs = np.linspace(6, 60, len(vals)); vmax = max(max(vals), 1)
                ys = 25 + np.array(vals) / vmax * 45
                ax.plot([6, 60], [25, 25], color="#24405E", lw=1, zorder=3)
                ax.fill_between(xs[:n], 25, ys[:n], color="#2DD4BF", alpha=.18 * e, zorder=3)
                ax.plot(xs[:n], ys[:n], color="#2DD4BF", lw=2.2, zorder=4)
                ax.add_patch(Circle((xs[n - 1], ys[n - 1]), 1.2, fc="#5EEAD4", zorder=5))
                T(6, 76, "Reported loss by week (USD, FX-normalized)", 8, "#8FA6BC", a=e)
                T(xs[n - 1], ys[n - 1] + 5, compact(vals[n - 1]), 8, "#5EEAD4", "bold", e, ha="center")
                T(6, 20, stats["weeks"][0] if stats["weeks"] else "", 6.5, "#8FA6BC", a=e)
                T(60, 20, stats["weeks"][-1] if stats["weeks"] else "", 6.5, "#8FA6BC", a=e, ha="right")
                cx, cy, r = 79, 55, 13
                ax.add_patch(Wedge((cx, cy), r, 0, 360, width=r * .22, fc="#0E1B2E", alpha=e, zorder=3))
                ax.add_patch(Wedge((cx, cy), r, 90, 90 - 360 * (stats["completeness"] / 100) * e, width=r * .22,
                                   fc="#FBBF24", alpha=.95 * e, zorder=4))
                T(cx, cy, f"{stats['completeness']*e:.0f}%", 14, "#F2F8FD", "bold", e, ha="center")
                T(cx, cy - 20, "Avg completeness", 8, "#8FA6BC", a=e, ha="center")
                T(cx, 20, f"Authorized settlements: {compact(stats['settled'])}", 7.5, "#C4B5FD", "bold", e, ha="center")
            else:
                T(50, 66, "Human-in-the-loop by design", 20, "#5EEAD4", "bold", e, ha="center")
                lines = ["Coverage & settlement require authorized approval",
                         "Every score explained · every decision audited",
                         "CSV / Excel intake with row-level validation",
                         "Local-first · SQLite · open-source · no API keys"]
                for i, s in enumerate(lines):
                    T(50, 52 - i * 8, "• " + s, 10, "#C9D6E3", a=ease(p * 2 - i * .25), ha="center")
                T(50, 14, "ClaimSight — synthetic demonstration · not regulated financial advice", 7.5, "#8FA6BC", a=e, ha="center")
            fade = max(0.0, 1 - p * 6) if p < .2 else (max(0.0, (p - .92) * 12) if p > .9 else 0)
            if fade > 0: ax.add_patch(Rectangle((0, 0), 100, 100, fc="#070D1A", alpha=min(1, fade), zorder=9))
            T(97, 3, f"{t:04.1f}s / {seconds:.0f}s", 6.5, "#5E7891", a=.9, ha="right", mono=True)
            fig.canvas.draw()
            writer.append_data(np.asarray(fig.canvas.buffer_rgba())[:, :, :3])
            if progress and f % 8 == 0: progress((f + 1) / total, f"Rendering frame {f+1}/{total}")
    finally:
        writer.close(); plt.close(fig)
    os.replace(tmp, VIDEO_PATH)
    meta = dict(generated_at=iso(now_utc()), seconds=seconds, fps=fps, width=W, height=H,
                frames=total, size_bytes=VIDEO_PATH.stat().st_size)
    VIDEO_PATH.with_suffix(".json").write_text(json.dumps(meta, indent=2))
    return meta

def _video_worker(stats: dict) -> None:
    try:
        render_demo_video(stats)
        with _VIDEO_LOCK: _VIDEO_STATE.update(state="ready", msg="")
    except Exception as e:
        with _VIDEO_LOCK: _VIDEO_STATE.update(state="error", msg=str(e))

def ensure_auto_video(stats: dict) -> None:
    if VIDEO_PATH.exists(): return
    with _VIDEO_LOCK:
        if _VIDEO_STATE["state"] == "rendering": return
        _VIDEO_STATE.update(state="rendering", msg="")
    threading.Thread(target=_video_worker, args=(stats,), daemon=True).start()

def tab_demo() -> None:
    section("Auto-generated live demo walkthrough (MP4)")
    st.caption("On first launch the app renders this walkthrough in the background from the live synthetic dataset — "
               "no screen recorder, no external tools. Regenerate any time at higher quality; download and share the file.")
    state = video_state()
    if state == "ready":
        meta = {}
        if VIDEO_PATH.with_suffix(".json").exists():
            meta = json.loads(VIDEO_PATH.with_suffix(".json").read_text())
        st.video(VIDEO_PATH.read_bytes(), format="video/mp4", autoplay=True, muted=True, loop=True)
        c1, c2 = st.columns([1, 1])
        c1.download_button("⬇ Download demo video (MP4)", VIDEO_PATH.read_bytes(), "claimsight_demo.mp4", "video/mp4",
                           type="primary", width="stretch", on_click=log_audit, args=("export", None, "demo_video"))
        c2.markdown(f'<div class="cs-card cs-mini">🎞 {meta.get("width", 848)}×{meta.get("height", 480)} · '
                    f'{meta.get("fps", 12)} fps · {meta.get("seconds", 14)}s · '
                    f'{meta.get("size_bytes", VIDEO_PATH.stat().st_size)/1e6:.1f} MB · generated {meta.get("generated_at", "—")}</div>',
                    unsafe_allow_html=True)
    elif state == "rendering":
        st.info("⏳ Walkthrough is rendering in the background (usually 10–30s). Keep using the app — this panel updates on your next interaction.")
    else:
        with _VIDEO_LOCK: err = _VIDEO_STATE["msg"]
        st.warning(f"Video not generated yet. {('Last error: ' + err) if err else 'Use Regenerate below.'}")
    with st.expander("🎬 Storyboard"):
        st.markdown("1. Brand intro → 2. Live intake KPIs + claim stream → 3. Severity bands + priority queue → "
                    "4. Weekly loss trend + completeness ring → 5. Human-approval boundaries. "
                    "All figures come from the current database at render time.")
    section("Regenerate at chosen quality")
    with st.form("video_form"):
        c1, c2, c3 = st.columns(3)
        res = c1.selectbox("Resolution", ["480p (848×480)", "720p (1280×720)"], key="demo_res")
        secs = c2.slider("Duration (s)", 8, 30, 14, key="demo_secs")
        fps = c3.selectbox("Frame rate", [12, 15, 24], key="demo_fps")
        go_btn = st.form_submit_button("🎥 Regenerate walkthrough", type="primary", width="stretch",
                                       disabled=video_state() == "rendering")
    if go_btn:
        size = (848, 480) if res.startswith("480") else (1280, 720)
        prog = st.progress(0.0, text="Preparing frames…")
        try:
            with _VIDEO_LOCK: _VIDEO_STATE.update(state="rendering", msg="")
            meta = render_demo_video(stats_snapshot(), seconds=secs, fps=fps, size=size,
                                     progress=lambda v, t: prog.progress(v, text=t))
            with _VIDEO_LOCK: _VIDEO_STATE.update(state="ready", msg="")
            log_audit("demo_video", None, meta)
            st.toast("🎬 Walkthrough regenerated", icon="🎬"); st.rerun()
        except Exception as e:
            with _VIDEO_LOCK: _VIDEO_STATE.update(state="error", msg=str(e))
            st.error(f"Render failed: {e}. Ensure imageio-ffmpeg installed (it bundles FFmpeg — no system install needed).")

# ============================================================ sidebar / state / main
def _role_changed() -> None:
    old = st.session_state.get("_prev_role", "Administrator"); new = st.session_state.role
    log_audit("role_switch", None, f"{old} → {new}", actor=ROLE_USER[new], role=new)
    st.session_state._prev_role = new

def init_state() -> None:
    ss = st.session_state
    defaults = dict(role="Administrator", _prev_role="Administrator", sim_running=True, sim_interval=4, sim_batch=1,
                    sim_bias=0.15, sim_anomaly=0.08, sim_autotriage=True, last_tick=time.monotonic(),
                    arrivals=[], last_crit_toast=0.0, undo=None, saved_views={},
                    rv_search="", rv_types=[], rv_bands=BAND_ORDER, rv_status=STATUS_OPEN, rv_sev=0,
                    rv_sort="Priority (live)", rv_arch=False, rv_docs=False, rv_breach=False)
    for k, v in defaults.items(): ss.setdefault(k, v)

def render_sidebar() -> None:
    with st.sidebar:
        st.markdown('<div class="cs-title" style="font-size:1.3rem;">ClaimSight</div>'
                    '<div class="cs-mini">Claims triage · loss analytics · governed decisions</div>', unsafe_allow_html=True)
        st.selectbox("Active role", ROLES, key="role", on_change=_role_changed)
        st.markdown(f'<div class="cs-card"><b>👤 {ROLE_USER[st.session_state.role]}</b>'
                    f'<div class="cs-mini">{len(PERMS[st.session_state.role])} permissions · '
                    f'{"decision authority ✔" if can("review_decide") else "decision authority 🔒"}</div></div>',
                    unsafe_allow_html=True)
        label = "⏸ Pause intake" if st.session_state.sim_running else "▶ Resume intake"
        if st.button(label, width="stretch"):
            st.session_state.sim_running = not st.session_state.sim_running
            log_audit("sim_toggle", None, "running" if st.session_state.sim_running else "paused")
        sidebar_live()
        with st.expander("▶ Run locally (Windows PowerShell)"):
            st.code("python -m venv .venv            # isolated environment\n"
                    ".\\.venv\\Scripts\\Activate.ps1   # activate\n"
                    "pip install -r requirements.txt  # dependencies\n"
                    "streamlit run app.py             # launch demo", language="powershell")
            st.caption("Everything runs offline after install · CPU-only · no API keys · data persists in claimsight_data/.")
        with st.expander("🔐 Governance boundaries"):
            st.caption("Coverage, settlement and severity-override actions are enforced server-side for Senior Reviewer / "
                       "Administrator only. Every mutation, decision and export writes an audit event. Synthetic data only — "
                       "no real customer information. Decision support, not regulated financial advice.")

def main() -> None:
    st.set_page_config(page_title=f"{APP_NAME} — Claims Triage Workbench", page_icon="🛡️", layout="wide",
                       initial_sidebar_state="expanded")
    init_state(); inject_css(); init_db(); seed_if_empty()
    ensure_auto_video(stats_snapshot())
    render_sidebar(); hero()
    tabs = st.tabs(["🛰️ Command Center", "📥 Intake", "🗂️ Register", "🚦 Triage Queue",
                    "📈 Analytics", "✅ Review & Approvals", "🧾 Reports & Audit", "🎬 Demo Studio"])
    with tabs[0]:
        command_center_live()
        with st.expander("ℹ️ About this demo"):
            st.markdown("**ClaimSight** organizes claim intake, completeness checks, severity analytics and triage queues. "
                        "It **does not** decide coverage or settlements — those stay with authorized humans, with reasons and audit. "
                        "The simulation starts automatically; steer it from the live controls above. Import the documented sample "
                        "files in **Intake**, work the **Triage Queue**, approve as **Senior Reviewer**, export from **Reports**, "
                        "and grab the auto-generated MP4 in **Demo Studio**. Deterministic engine "
                        f"**{RULES_VERSION}** · reference FX **{FX_VERSION}** · seeded synthetic dataset (seed 42).")
    with tabs[1]: tab_intake()
    with tabs[2]: tab_register()
    with tabs[3]: tab_triage()
    with tabs[4]: tab_analytics()
    with tabs[5]: tab_review()
    with tabs[6]: tab_reports()
    with tabs[7]: tab_demo()
    st.markdown('<div class="cs-footer">ClaimSight · decision-support prototype · synthetic data only · coverage &amp; settlement '
                'decisions require authorized human approval · not regulated financial advice · engine RULES-1.3.0 · '
                'all actions audited</div>', unsafe_allow_html=True)

main()