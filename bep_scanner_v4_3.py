
import streamlit as st
import pandas as pd
import numpy as np
from datetime import datetime, timedelta, date, time as dtime
import time
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple
import plotly.graph_objects as go
from plotly.subplots import make_subplots
import json
import os
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from urllib.parse import quote
import pytz

# IST timezone — used everywhere for consistent datetime comparisons
IST = pytz.timezone('Asia/Kolkata')

# ============================================================
# BEP BREAK-EVEN POINT SCANNER PRO v4.3
# NEW in v4.3:
#   FIX — Hover side close < BEP enforced at candle T:
#     The hover condition used close < BEP+5 as a wide net (covering
#     Pattern B: just-crossed candles where close is between BEP and BEP+5).
#     But the spec requires the hover side to be WEAK (close < BEP) at T
#     as a separate explicit check. This was missing — Pattern B candles
#     (close above BEP at T) were incorrectly qualifying as hover signals.
#     Fix: added `hover_row['close'] >= hover_bep → skip` immediately after
#     the hover condition, mirroring the same check already done at T+1.
#   OPTIMIZATIONS (no logic changes):
#   OPT 1 — _strikes property: strike range computed once, used in 4 methods.
#   OPT 2 — Eliminated duplicate method calls per rerun: confluence/confirmed/
#     breakout computed once, cached in session_state for metrics + UI blocks.
#   OPT 3 — len(list(strikes)) → len(strikes): range supports len() natively.
#   OPT 4 — detect_bep_breakout: pre-indexed candle dataframes for O(log n)
#     next-candle lookup instead of O(n) boolean scan per call.
# NEW in v4.0:
#   BREAKOUT logic:
#   - Hover condition unified: open < BEP AND high >= BEP+1 AND close < BEP+5
#     Pattern A (tried & failed): close < BEP
#     Pattern B (just crossed):   BEP <= close < BEP+5
#     Eliminates deep ITM strikes already far above BEP from firing
#   - 09:25 filter: hover candle T and breakout candle T+1 must both
#     be at 09:25 or later — skips first two opening candles (09:15, 09:20)
#     to eliminate BTST/opening-noise false signals
#   Streamlit deprecation fixes:
#   - All use_container_width=True  → width='stretch'
#   - All use_container_width=False → width='content'
#   - st.components.v1.html kept for JS injection (st.iframe rejects height=0)
# NEW in v3.15 (BEP BREAKOUT overhaul):
#   - detect_bep_breakout rewritten: hover is standalone trigger (no S/R needed)
#   - Exact candle match (< 30s), T+1 only confirmation window
#   - Hover side close checked at both T and T+1
#   - detect_bep_breakout completely rewritten:
#     * Hover condition: open < BEP AND high >= BEP+1 (high must be at least 1pt above BEP)
#     * Hover candle matched with exact timestamp (< 30s tolerance, was ±300s — fixed wrong candle bug)
#     * Hover side (CE for BUY PE, PE for BUY CE) close must be < BEP at BOTH T and T+1
#     * Confirmation window: T+1 strictly (one candle only, was 2)
#     * Breakout side: open AND close both > BEP at T+1
#     * Invalidated if hover side close >= BEP at T+1
#     * No longer depends on existing RESISTANCE signal — hover candle IS the trigger
#     * Symmetric: BUY PE (CE hovers) and BUY CE (PE hovers) both supported
#   - _build_breakout_telegram_message updated:
#     * Shows hover candle OHLC at T
#     * Shows hover side close at T+1 with below-BEP confirmation
#     * Uses hover_time / confirm_time instead of signal_time
#   - UI expander display updated to match new dict fields
#   - Dedup key unchanged: action + confirm_time + breakout_strike + opt
# NEW in v3.14 (confluence rule fix + bug fixes):
#   - get_confluence_signals: strict CE+PE cross-side validation
#   - get_confluence_signals: strict CE+PE cross-side validation
#     Valid:   CE RESISTANCE + PE SUPPORT → BUY
#              CE SUPPORT    + PE RESISTANCE → SELL
#     Blocked: CE RES + PE RES  (same direction, no SUPPORT)
#              CE SUP + PE SUP  (same direction, no RESISTANCE)
#              CE RES + CE SUP  (both CE, no PE involved)
#              PE RES + PE SUP  (both PE, no CE involved)
#   - confirm_confluence: direction now derived from the canonical CE/PE
#     cross pair directly, not from a fragile ce_sigs[0] guess
#   - BEP BREAKOUT dedup key changed to action+confirm_time+breakout_strike
#     (was action+signal_time+confirm_time+breakout_strike) — prevents
#     duplicate Telegram alerts when multiple resistance strikes trigger
#     the same breakout candle at different earlier times
#   - Restored missing `def test_telegram_connection(...)` — was a NameError
#     crash whenever "Test Telegram" button was clicked
#   - access_token input moved above Re-centre ATM button — fixes silent
#     UnboundLocalError on first Streamlit run
#   - Removed redundant `import requests as _req` inside Telegram loop
# NEW in v3.13 (BEP BREAKOUT hover fix):
#   - Fixed hover condition: open < BEP AND high >= BEP
# NEW in v3.12 (BEP BREAKOUT ALERT):
#   - New alert type: BEP BREAKOUT ALERT (separate from confluence)
#   - BUY CE: any PE fires full RESISTANCE + CE high >= CE BEP at same candle
#     → within next 2 candles, any CE open AND close both > CE BEP → BUY CE
#   - BUY PE (mirror): any CE fires full RESISTANCE + PE high >= PE BEP at same candle
#     → within next 2 candles, any PE open AND close both > PE BEP → BUY PE
#   - Different strikes allowed for CE and PE
#   - Fires every time condition is freshly met (no daily dedup)
#   - Displayed inline in existing confluence expanders
#   - Telegram alert: "BUY CE" / "BUY PE" in green, with SL = low of breakout candle
# NEW in v3.11 (looser wick threshold):
#   - SUPPORT wick: low <= BEP - 1.5 (was BEP - 3)
#   - RESISTANCE wick: high >= BEP + 1.5 (was BEP + 3)
#   - Close and open rules unchanged
# NEW in v3.10 (looser close threshold):
#   - SUPPORT close: >= BEP + 1 (was BEP + 3)
#   - RESISTANCE close: <= BEP - 1 (was BEP - 3)
#   - Wick and open rules unchanged
# NEW in v3.9 (signals table improvements):
#   - Raw Signals metric restored (5 metrics now)
#   - BEP Signals table shows ALL raw signals (not just confluence)
#   - Added Confluence Yes/No column to table
#   - Table renamed to "BEP Signals"
# NEW in v3.8 (two-stage confluence):
#   - Stage 1 WAIT alert: SUPPORT + RESISTANCE detected at same candle
#   - Stage 2 BUY/SELL alert: confirmed when resistance stays below BEP
#     and support recovers above BEP within 4 candles
#   - Invalidated if resistance closes above BEP at any point in window
#   - CE RESISTANCE + PE SUPPORT → BUY; mirror → SELL
# NEW in v3.7 (stricter rejection rules):
#   - SUPPORT: open >= BEP+0.4, close >= BEP+3, wick <= BEP-3
#   - RESISTANCE: open <= BEP-0.4, close <= BEP-3, wick >= BEP+3
# NEW in v3.6 (confluence fix):
#   - Confluence now requires one SUPPORT + one RESISTANCE at same candle time
#   - Two SUPPORTs or two RESISTANCEs no longer trigger confluence alert
# NEW in v2.9 (live market improvements):
#   - Incremental live scan: only fetches latest closed 5-min candle
#   - Confluence fires correctly during live market
#   - Live countdown timer shows next auto-refresh
#   - Market status indicator (Pre/Open/Closed)
#   - Last candle time shown per strike in BEP table
#   - Full history scan preserved for after-market use
# ============================================================


@dataclass
class Signal:
    strike: int
    option_type: str
    bep: float
    candle_time: datetime
    open: float
    high: float
    low: float
    close: float
    signal_type: str
    wick_low: float
    wick_high: float
    body_bottom: float
    body_top: float

    def to_dict(self, include_meta: bool = False):
        d = {
            'Date': self.candle_time.strftime('%Y-%m-%d'),
            'Candle Time': self.candle_time.strftime('%H:%M'),
            'Strike': self.strike,
            'Type': self.option_type,
            'Signal': self.signal_type,
            'BEP': round(self.bep, 2),
            'Open': round(self.open, 2),
            'High': round(self.high, 2),
            'Low': round(self.low, 2),
            'Close': round(self.close, 2),
            'Wick Low': round(self.wick_low, 2),
            'Wick High': round(self.wick_high, 2),
        }
        if include_meta:
            d['Detected At'] = datetime.now().strftime('%H:%M:%S')
        return d


def create_retry_session(retries=3, backoff_factor=1,
                         status_forcelist=(429, 500, 502, 503, 504)):
    session = requests.Session()
    retry = Retry(total=retries, read=retries, connect=retries,
                  backoff_factor=backoff_factor, status_forcelist=status_forcelist)
    adapter = HTTPAdapter(max_retries=retry, pool_connections=10, pool_maxsize=20)
    session.mount('https://', adapter)
    session.mount('http://', adapter)
    return session


class UpstoxBEPScanner:
    def __init__(self, access_token: str, atm_strike: int,
                 strike_range: int = 10, target_expiry: Optional[date] = None):
        self.access_token = access_token
        self.atm_strike = atm_strike
        self.strike_range = strike_range
        self.base_url = "https://api.upstox.com/v3"
        self.headers = {
            'Authorization': f'Bearer {access_token}',
            'Accept': 'application/json',
            'Content-Type': 'application/json'
        }
        self.signals: List[Signal] = []
        self.bep_data: Dict[str, float] = {}
        self.raw_pdc: Dict[str, float] = {}
        self.candle_history: Dict[str, pd.DataFrame] = {}
        self.session = create_retry_session()
        self.target_expiry: Optional[date] = target_expiry
        self.instruments_lookup: Dict[Tuple[int, str], str] = {}
        self.last_errors: List[str] = []

    @property
    def _strikes(self) -> range:
        """Strike range computed once — used by calculate_all_beps,
        scan_all_strikes, scan_latest_candle, fetch_instruments_from_api."""
        return range(
            self.atm_strike - self.strike_range * 50,
            self.atm_strike + self.strike_range * 50 + 1,
            50
        )

    # ------------------------------------------------------------------
    # Fetch instruments live from Upstox search API
    # ------------------------------------------------------------------
    def fetch_instruments_from_api(self) -> Tuple[int, List[str]]:
        """Fetch NIFTY option instruments for the chosen expiry from Upstox v2 search API."""
        if not self.target_expiry:
            return 0, ["No expiry date selected."]

        errors = []
        lookup: Dict[Tuple[int, str], str] = {}
        strikes = list(self._strikes)
        search_url = "https://api.upstox.com/v2/instruments/search"
        debug_sample = {}   # store first raw response for diagnostics

        for strike in strikes:
            for opt in ['CE', 'PE']:
                try:
                    resp = self.session.get(
                        search_url,
                        headers=self.headers,
                        params={'query': f'NIFTY {strike} {opt}',
                                'instrument_type': 'OPTIDX'},
                        timeout=10
                    )
                    if resp.status_code != 200:
                        errors.append(f"{strike}{opt}: HTTP {resp.status_code}")
                        time.sleep(0.1)
                        continue

                    items = resp.json().get('data', [])
                    if items and not debug_sample:
                        debug_sample = items[0]   # capture first item for debug
                    matched_key = None

                    for item in items:
                        name  = str(item.get('name', '')).upper().strip()
                        asset = str(item.get('asset_symbol', '')).upper().strip()
                        # Must be NIFTY index (exclude BANKNIFTY, MIDCPNIFTY, FINNIFTY)
                        if 'NIFTY' not in name and 'NIFTY' not in asset:
                            continue
                        if any(x in name for x in ['BANK', 'MIDCP', 'FIN']):
                            continue
                        # Match strike
                        s = item.get('strike_price')
                        if s is None or int(float(s)) != strike:
                            continue
                        # Match option type
                        if str(item.get('instrument_type', '')).upper().strip() != opt:
                            continue
                        # Match expiry date
                        # Upstox returns expiry as string "YYYY-MM-DD" or int epoch-ms
                        exp_raw = item.get('expiry')
                        if exp_raw:
                            try:
                                if isinstance(exp_raw, str):
                                    # e.g. "2026-06-12" or "12-06-2026"
                                    for fmt in ('%Y-%m-%d', '%d-%m-%Y', '%Y/%m/%d'):
                                        try:
                                            exp_date = datetime.strptime(exp_raw[:10], fmt).date()
                                            break
                                        except ValueError:
                                            continue
                                    else:
                                        continue   # unrecognised format, skip
                                else:
                                    # integer epoch milliseconds
                                    exp_date = datetime.fromtimestamp(int(exp_raw) / 1000).date()
                                if exp_date != self.target_expiry:
                                    continue
                            except Exception:
                                continue
                        inst_key = item.get('instrument_key', '')
                        if inst_key:
                            matched_key = inst_key
                            break

                    if matched_key:
                        lookup[(strike, opt)] = matched_key
                    else:
                        errors.append(
                            f"{strike}{opt} ({self.target_expiry}): No match in API results"
                        )
                    time.sleep(0.12)

                except Exception as e:
                    errors.append(f"{strike}{opt}: {str(e)[:80]}")

        self.instruments_lookup = lookup
        self.debug_sample = debug_sample
        return len(lookup), errors

    def _build_instrument_key_direct(self, strike: int, opt: str) -> Optional[str]:
        """
        Fallback: construct NSE_FO instrument key directly.
        Upstox NSE_FO index option key format examples:
          NSE_FO|NIFTY2561223400CE   (YY + MonthAbbr-num + DD is NOT used)
          Actual format: NSE_FO|NIFTY<YY><MMM><DD><STRIKE><OPT>
          where MMM is 3-letter month e.g. JUN, SEP
        Example for 12 Jun 2026, strike 23400 CE:
          NSE_FO|NIFTY26JUN2326400CE  — Upstox uses this older format for weekly
        Safer format used by Upstox for index weekly options:
          NSE_FO|NIFTY<YY><M><DD><STRIKE><OPT>  e.g. NIFTY2661223400CE
        We try two patterns and return the first.
        """
        if not self.target_expiry:
            return None
        exp = self.target_expiry
        yy  = exp.strftime('%y')          # "26"
        mm  = exp.strftime('%m')          # "06"
        dd  = exp.strftime('%d')          # "12"
        mon = exp.strftime('%b').upper()  # "JUN"
        # Pattern 1: NIFTY26JUN1223400CE  (monthly/popular strikes)
        key1 = f"NSE_FO|NIFTY{yy}{mon}{dd}{strike}{opt}"
        return key1

    def get_instrument_key(self, strike: int, opt: str) -> Tuple[Optional[str], str]:
        opt = opt.upper().strip()
        key = (int(strike), opt)
        if key in self.instruments_lookup:
            return self.instruments_lookup[key], "api_search"
        direct = self._build_instrument_key_direct(strike, opt)
        if direct:
            return direct, "direct_construct"
        return None, "not_found"

    # ------------------------------------------------------------------
    # Generic API call
    # ------------------------------------------------------------------
    def _make_api_call(self, url: str,
                       params: Optional[dict] = None) -> Tuple[Optional[dict], Optional[str]]:
        try:
            resp = self.session.get(url, headers=self.headers, params=params, timeout=15)
            if resp.status_code == 401:
                return None, "Unauthorized – Token expired or invalid"
            elif resp.status_code == 404:
                return None, "Not Found (404) – check instrument key format"
            elif resp.status_code == 429:
                return None, "Rate limited (429) – wait and retry"
            elif resp.status_code == 400:
                # Capture the actual Upstox error message for debugging
                try:
                    body = resp.json()
                    msg = body.get('message') or body.get('errors') or str(body)[:120]
                except Exception:
                    msg = resp.text[:120]
                return None, f"Bad Request (400): {msg}"
            resp.raise_for_status()
            return resp.json(), None
        except requests.exceptions.ConnectionError as e:
            return None, f"Connection error: {str(e)[:100]}"
        except requests.exceptions.Timeout:
            return None, "Request timeout"
        except requests.exceptions.HTTPError as e:
            try:
                body = resp.json()
                msg = body.get('message') or str(body)[:120]
            except Exception:
                msg = resp.text[:120]
            return None, f"HTTP {resp.status_code}: {msg}"
        except Exception as e:
            return None, f"Unexpected error: {str(e)[:100]}"

    # ------------------------------------------------------------------
    # Nifty spot LTP — used for Re-centre ATM
    # Uses Upstox v2 market quote for NSE_INDEX|Nifty 50
    # ------------------------------------------------------------------
    def fetch_nifty_spot(self) -> Tuple[Optional[float], Optional[str]]:
        """Fetch current Nifty 50 spot LTP from Upstox market quotes API."""
        # Upstox instrument key for Nifty 50 index
        nifty_key = "NSE_INDEX|Nifty 50"
        encoded   = quote(nifty_key, safe='')
        # v2 market quote endpoint
        url = f"https://api.upstox.com/v2/market-quote/quotes"
        try:
            resp = self.session.get(
                url,
                headers=self.headers,
                params={"symbol": nifty_key},
                timeout=10
            )
            if resp.status_code == 200:
                data = resp.json()
                # Response: data -> {instrument_key: {last_price: ...}}
                quote_data = data.get("data", {})
                for key_name, val in quote_data.items():
                    ltp = val.get("last_price") or val.get("ltp")
                    if ltp:
                        return float(ltp), None
            # Fallback: try LTP endpoint
            url2 = f"https://api.upstox.com/v2/market-quote/ltp"
            resp2 = self.session.get(
                url2,
                headers=self.headers,
                params={"symbol": nifty_key},
                timeout=10
            )
            if resp2.status_code == 200:
                data2 = resp2.json()
                quote_data2 = data2.get("data", {})
                for key_name, val in quote_data2.items():
                    ltp = val.get("last_price") or val.get("ltp")
                    if ltp:
                        return float(ltp), None
            return None, f"HTTP {resp.status_code} from market quote API"
        except Exception as e:
            return None, str(e)[:100]

    # ------------------------------------------------------------------
    # Previous day close
    # Upstox v2 historical candle:
    #   GET /v2/historical-candle/{instrument_key}/day/{to_date}/{from_date}
    #   instrument_key must be URL-encoded in the PATH (pipe | → %7C)
    # ------------------------------------------------------------------
    def fetch_previous_day_close(self, instrument_key: str) -> Tuple[Optional[float], Optional[str]]:
        if not instrument_key:
            return None, "No instrument key provided"
        # URL-encode the pipe character in instrument key for path segment
        encoded_key = quote(instrument_key, safe='')
        to_date   = datetime.now().strftime('%Y-%m-%d')
        from_date = (datetime.now() - timedelta(days=7)).strftime('%Y-%m-%d')

        # Try v2 endpoint first (more stable for historical)
        url = f"https://api.upstox.com/v2/historical-candle/{encoded_key}/day/{to_date}/{from_date}"
        data, error = self._make_api_call(url)

        if error:
            # Fallback: try v3 endpoint
            url_v3 = f"https://api.upstox.com/v3/historical-candle/{encoded_key}/day/{to_date}/{from_date}"
            data, error = self._make_api_call(url_v3)
            if error:
                return None, error

        if data and data.get('status') == 'success':
            candle_data = data.get('data', {})
            # v2 returns data.candles; v3 returns data directly as list
            if isinstance(candle_data, dict):
                candles = candle_data.get('candles', [])
            elif isinstance(candle_data, list):
                candles = candle_data
            else:
                candles = []

            if not candles:
                return None, "Empty candle data"

            # candles[0] is ALWAYS the last fully closed market day (PDC).
            # No clock check needed here — Upstox never returns partial/live
            # data in the historical-candle/day endpoint.
            # Live market comparison logic lives in scan_latest_candle().
            return float(candles[0][4]), None

        return None, "No candle data in response"

    # ------------------------------------------------------------------
    # Intraday 5-min candles
    # v2: /v2/historical-candle/intraday/{key}/5minute
    # v3: /v3/historical-candle/intraday/{key}/minutes/5
    # ------------------------------------------------------------------
    def fetch_intraday_candles(self, instrument_key: str) -> Tuple[Optional[pd.DataFrame], Optional[str]]:
        if not instrument_key:
            return None, "No instrument key provided"
        encoded_key = quote(instrument_key, safe='')

        # Try v2 first, then v3 as fallback
        for url in [
            f"https://api.upstox.com/v2/historical-candle/intraday/{encoded_key}/5minute",
            f"https://api.upstox.com/v3/historical-candle/intraday/{encoded_key}/minutes/5",
        ]:
            data, error = self._make_api_call(url)
            if error:
                last_error = error
                continue
            if data and data.get('status') == 'success':
                raw = data.get('data', {})
                candles = raw.get('candles', []) if isinstance(raw, dict) else (raw if isinstance(raw, list) else [])
                if candles:
                    df = pd.DataFrame(candles,
                                      columns=['timestamp','open','high','low','close','volume','oi'])
                    df['timestamp'] = pd.to_datetime(df['timestamp'], utc=True).dt.tz_convert('Asia/Kolkata')
                    df = df.sort_values('timestamp').reset_index(drop=True)
                    for col in ['open','high','low','close','volume','oi']:
                        df[col] = pd.to_numeric(df[col], errors='coerce')
                    return df, None
            last_error = "Empty candle list"

        return None, last_error

    # ------------------------------------------------------------------
    # BEP calculation
    # ------------------------------------------------------------------
    def calculate_all_beps(self) -> Tuple[pd.DataFrame, List[str]]:
        self.raw_pdc = {}
        errors = []
        strikes = self._strikes
        total = len(strikes) * 2
        progress = st.progress(0)
        processed = 0

        for strike in strikes:
            for opt in ['CE', 'PE']:
                key = f"{strike}_{opt}"
                inst_key, source = self.get_instrument_key(strike, opt)
                if not inst_key:
                    errors.append(f"{key}: Not found ({source})")
                else:
                    pdc, error = self.fetch_previous_day_close(inst_key)
                    if pdc is not None:
                        self.raw_pdc[key] = pdc
                    else:
                        errors.append(f"{key} [{source}]: {error}")
                processed += 1
                progress.progress(min(processed / total, 0.99))
                time.sleep(0.3)

        progress.empty()
        self.bep_data = {}
        table_rows = []
        for strike in strikes:
            ce_pdc = self.raw_pdc.get(f"{strike}_CE")
            pe_pdc = self.raw_pdc.get(f"{strike}_PE")
            if ce_pdc and pe_pdc:
                bep = (ce_pdc + pe_pdc) / 2
                self.bep_data[f"{strike}_CE"] = bep
                self.bep_data[f"{strike}_PE"] = bep
                table_rows.append({
                    'Strike': strike,
                    'CE PDC': round(ce_pdc, 2),
                    'PE PDC': round(pe_pdc, 2),
                    'BEP': round(bep, 2),
                })
        return pd.DataFrame(table_rows), errors

    # ------------------------------------------------------------------
    # Rejection detection — both CE and PE check SUPPORT and RESISTANCE
    # ------------------------------------------------------------------
    def detect_rejection(self, df: pd.DataFrame, bep: float,
                          opt_type: str, strike: int) -> List[Signal]:
        signals = []
        for _, row in df.iterrows():
            o, h, l, c = row['open'], row['high'], row['low'], row['close']
            bb = min(o, c)   # body bottom
            bt = max(o, c)   # body top
            body_size   = bt - bb                  # full body size
            lower_wick  = bb - l                   # wick below body
            upper_wick  = h - bt                   # wick above body
            half_body   = body_size / 2            # minimum wick requirement

            # ── SUPPORT ───────────────────────────────────────────────
            # Rule 1: lower wick >= half the body size
            # Rule 2: wick must penetrate at least 1.5 pts below BEP
            # Rule 3: open at least 0.4 pts above BEP
            # Rule 4: close at least 1 pt above BEP
            if (lower_wick >= half_body and
                    l <= bep - 1.5 and
                    o >= bep + 0.4 and
                    c >= bep + 1):
                signals.append(Signal(
                    strike=strike, option_type=opt_type, bep=bep,
                    candle_time=row['timestamp'], open=o, high=h, low=l, close=c,
                    signal_type='SUPPORT',
                    wick_low=l, wick_high=h, body_bottom=bb, body_top=bt
                ))

            # ── RESISTANCE ────────────────────────────────────────────
            # Rule 1: upper wick >= half the body size
            # Rule 2: wick must penetrate at least 1.5 pts above BEP
            # Rule 3: open at least 0.4 pts below BEP
            # Rule 4: close at least 1 pt below BEP
            elif (upper_wick >= half_body and
                    h >= bep + 1.5 and
                    o <= bep - 0.4 and
                    c <= bep - 1):
                signals.append(Signal(
                    strike=strike, option_type=opt_type, bep=bep,
                    candle_time=row['timestamp'], open=o, high=h, low=l, close=c,
                    signal_type='RESISTANCE',
                    wick_low=l, wick_high=h, body_bottom=bb, body_top=bt
                ))
        return signals

    # ------------------------------------------------------------------
    # Scan all strikes
    # ------------------------------------------------------------------
    def scan_all_strikes(self) -> Tuple[List[Signal], List[str]]:
        all_signals = []
        errors = []
        if not self.bep_data:
            return all_signals, ["BEP data not calculated. Run Calculate BEPs first."]

        strikes = self._strikes
        progress = st.progress(0)
        total = len(strikes) * 2
        processed = 0

        for strike in strikes:
            for opt in ['CE', 'PE']:
                key = f"{strike}_{opt}"
                bep = self.bep_data.get(key)
                if bep:
                    inst_key, source = self.get_instrument_key(strike, opt)
                    if not inst_key:
                        errors.append(f"{key}: No instrument key found")
                    else:
                        df, error = self.fetch_intraday_candles(inst_key)
                        if df is not None and not df.empty:
                            self.candle_history[key] = df
                            sigs = self.detect_rejection(df, bep, opt, strike)
                            all_signals.extend(sigs)
                        else:
                            errors.append(f"{key}: {error}")
                processed += 1
                progress.progress(min(processed / total, 0.99))
                time.sleep(0.3)

        progress.empty()
        self.signals = all_signals
        return all_signals, errors

    def get_signals_grouped_by_time(self) -> Dict[str, List[Signal]]:
        grouped: Dict[str, List[Signal]] = {}
        for sig in self.signals:
            tk = sig.candle_time.strftime('%H:%M')
            grouped.setdefault(tk, []).append(sig)
        return grouped

    def get_confluence_signals(self) -> Dict[str, List[Signal]]:
        """
        Stage 1 — WAIT alert.
        Valid confluence requires ALL of:
          - At least one CE signal and at least one PE signal (cross-type mandatory)
          - At least one SUPPORT and at least one RESISTANCE (cross-direction mandatory)
          - The CE and PE must be on OPPOSITE sides:
              CE RESISTANCE + PE SUPPORT  → BUY setup
              CE SUPPORT    + PE RESISTANCE → SELL setup
        Rejected combinations:
          CE RES + PE RES  ❌  (same direction, no support)
          CE SUP + PE SUP  ❌  (same direction, no resistance)
          CE RES + CE SUP  ❌  (no PE involved)
          PE RES + PE SUP  ❌  (no CE involved)
        """
        grouped = self.get_signals_grouped_by_time()
        confluence = {}
        for time_key, sigs in grouped.items():
            ce_sigs = [s for s in sigs if s.option_type == 'CE']
            pe_sigs = [s for s in sigs if s.option_type == 'PE']

            # Must have at least one CE and one PE
            if not ce_sigs or not pe_sigs:
                continue

            ce_has_res = any(s.signal_type == 'RESISTANCE' for s in ce_sigs)
            ce_has_sup = any(s.signal_type == 'SUPPORT'    for s in ce_sigs)
            pe_has_res = any(s.signal_type == 'RESISTANCE' for s in pe_sigs)
            pe_has_sup = any(s.signal_type == 'SUPPORT'    for s in pe_sigs)

            # Valid patterns only:
            #   CE RESISTANCE + PE SUPPORT  → BUY
            #   CE SUPPORT    + PE RESISTANCE → SELL
            valid_buy  = ce_has_res and pe_has_sup
            valid_sell = ce_has_sup and pe_has_res

            if valid_buy or valid_sell:
                confluence[time_key] = sigs
        return confluence

    def confirm_confluence(self, max_candles: int = 4) -> Dict[str, Dict]:
        """
        Stage 2 — BUY / SELL confirmation.

        For each valid confluence (CE RES + PE SUP → BUY, or CE SUP + PE RES → SELL):
          - Walk the next 1–max_candles candles in candle_history
          - RESISTANCE close must stay BELOW its BEP on every checked candle
            (if it crosses above BEP at any point → INVALIDATED)
          - Confirmation fires on the first candle where BOTH:
              RESISTANCE close < BEP  AND  SUPPORT close > BEP

        CE RESISTANCE + PE SUPPORT → action = BUY
        CE SUPPORT + PE RESISTANCE → action = SELL

        Returns dict keyed by signal_time:
          { signal_time, confirm_time, action, sigs, status }
          status: 'CONFIRMED' | 'PENDING' | 'INVALIDATED'
        """
        potential = self.get_confluence_signals()
        results = {}

        for time_key, sigs in potential.items():
            ce_sigs = [s for s in sigs if s.option_type == 'CE']
            pe_sigs = [s for s in sigs if s.option_type == 'PE']

            # Identify the canonical cross pair for this confluence
            ce_res_sigs = [s for s in ce_sigs if s.signal_type == 'RESISTANCE']
            ce_sup_sigs = [s for s in ce_sigs if s.signal_type == 'SUPPORT']
            pe_res_sigs = [s for s in pe_sigs if s.signal_type == 'RESISTANCE']
            pe_sup_sigs = [s for s in pe_sigs if s.signal_type == 'SUPPORT']

            # CE RES + PE SUP → BUY; CE SUP + PE RES → SELL
            if ce_res_sigs and pe_sup_sigs:
                res_sig = ce_res_sigs[0]
                sup_sig = pe_sup_sigs[0]
                action  = 'BUY'
            elif ce_sup_sigs and pe_res_sigs:
                sup_sig = ce_sup_sigs[0]
                res_sig = pe_res_sigs[0]
                action  = 'SELL'
            else:
                continue  # shouldn't happen after get_confluence_signals filter

            sup_key = f"{sup_sig.strike}_{sup_sig.option_type}"
            res_key = f"{res_sig.strike}_{res_sig.option_type}"

            sup_df = self.candle_history.get(sup_key)
            res_df = self.candle_history.get(res_key)

            if sup_df is None or res_df is None:
                results[time_key] = dict(
                    signal_time=time_key, confirm_time=None,
                    action=action, sigs=sigs, status='PENDING'
                )
                continue

            signal_dt = sup_sig.candle_time
            sup_after = sup_df[sup_df['timestamp'] > signal_dt].head(max_candles)
            res_after = res_df[res_df['timestamp'] > signal_dt].head(max_candles)

            if sup_after.empty or res_after.empty:
                results[time_key] = dict(
                    signal_time=time_key, confirm_time=None,
                    action=action, sigs=sigs, status='PENDING'
                )
                continue

            bep_sup = sup_sig.bep
            bep_res = res_sig.bep
            status = 'PENDING'
            conf_time = None
            invalidated = False

            for i in range(len(res_after)):
                res_row = res_after.iloc[i]

                # Invalidate if resistance breaks above its BEP at any candle
                if res_row['close'] > bep_res:
                    invalidated = True
                    break

                # Find support candle matching same 5-min slot (within 300s)
                sup_match = sup_after[
                    (sup_after['timestamp'] - res_row['timestamp'])
                    .dt.total_seconds().abs() <= 300
                ]
                if sup_match.empty:
                    continue

                sup_row = sup_match.iloc[0]

                # Both conditions met simultaneously → confirmed
                if res_row['close'] < bep_res and sup_row['close'] > bep_sup:
                    status = 'CONFIRMED'
                    conf_time = res_row['timestamp'].strftime('%H:%M')
                    break

            if invalidated:
                status = 'INVALIDATED'

            results[time_key] = dict(
                signal_time=time_key, confirm_time=conf_time,
                action=action, sigs=sigs, status=status
            )

        return results

    # ------------------------------------------------------------------
    # BEP BREAKOUT ALERT detection
    # ------------------------------------------------------------------
    def detect_bep_breakout(self) -> List[Dict]:
        """
        BEP BREAKOUT ALERT — v4.0

        Hover condition (unified — covers all 3 patterns):
          open < BEP  AND  high >= BEP+1  AND  low <= BEP-1  AND  close < BEP+5
          Pattern A (tried & failed): open<BEP, high>=BEP+1, low<=BEP-1, close<BEP
          Pattern B (just crossed):   open<BEP, high>=BEP+1, low<=BEP-1, BEP<=close<BEP+5
          Pattern C (rejected both):  open<BEP, high>=BEP+1, low<=BEP-1, close<BEP
          Candle must straddle BEP on BOTH sides — genuine BEP interaction

        BUY PE:
          T   — CE strike satisfies hover condition (open<BEP, high>=BEP+1,
                low<=BEP-1, close<BEP+5) AND CE close < CE_BEP (still weak at T)
          T+1 — PE open > PE_BEP AND PE close > PE_BEP (confirmed above)
                CE close < CE_BEP (still weak at T+1)
          → BUY PE

        BUY CE (mirror):
          T   — PE strike satisfies hover condition AND PE close < PE_BEP (still weak at T)
          T+1 — CE open > CE_BEP AND CE close > CE_BEP
                PE close < PE_BEP (still weak at T+1)
          → BUY CE

        Filters:
          - Hover candle T must be at 09:25 or later (skip first two candles)
          - T+1 candle must also be at 09:25 or later
          - Confirmation window: T+1 strictly (one candle only)
          - Different strikes allowed across CE and PE
        """
        results              = []
        MARKET_OPEN_FILTER   = dtime(9, 25)   # skip 09:15 and 09:20 candles

        # Pre-index all dataframes by timestamp for O(1) next-candle lookup.
        # Without this, get_next_candle does a full O(n) boolean scan of the
        # dataframe on every (hover_candle × breakout_strike) pair — which is
        # O(strikes² × candles) per detect_bep_breakout call.
        # With a sorted index, searchsorted gives O(log n) per lookup.
        indexed: Dict[str, pd.DataFrame] = {}
        for k, df in self.candle_history.items():
            if df is not None and not df.empty:
                indexed[k] = df.set_index('timestamp').sort_index()

        def get_next_candle(df: pd.DataFrame, signal_dt: datetime) -> Optional[pd.Series]:
            """Return the first candle strictly after signal_dt using sorted index."""
            after = df[df.index > signal_dt]
            return after.iloc[0] if not after.empty else None

        for hover_key, hover_df in self.candle_history.items():
            if hover_df is None or hover_df.empty:
                continue
            hover_bep = self.bep_data.get(hover_key)
            if hover_bep is None:
                continue
            is_ce_hover = hover_key.endswith('_CE')
            is_pe_hover = hover_key.endswith('_PE')
            if not is_ce_hover and not is_pe_hover:
                continue

            hover_idx      = indexed.get(hover_key)
            breakout_suffix = '_PE' if is_ce_hover else '_CE'
            action          = 'BUY PE' if is_ce_hover else 'BUY CE'

            for _, hover_row in hover_df.iterrows():
                signal_dt = hover_row['timestamp']

                # ── 09:25 filter — skip first two opening candles ─────────
                if signal_dt.time() < MARKET_OPEN_FILTER:
                    continue

                # ── Unified hover condition ───────────────────────────────
                # Candle must straddle BEP on both sides:
                #   open  < BEP         — opened below BEP
                #   high  >= BEP+1      — wick at least 1pt above BEP
                #   low   <= BEP-1      — wick at least 1pt below BEP
                #   close < BEP+5       — didn't close far above BEP (wide net)
                if not (hover_row['open']  < hover_bep      and
                        hover_row['high']  >= hover_bep + 1 and
                        hover_row['low']   <= hover_bep - 1 and
                        hover_row['close'] < hover_bep + 5):
                    continue

                # ── Hover side still weak at T ────────────────────────────
                # close < BEP+5 above is a wide net that also allows Pattern B
                # (just crossed: BEP <= close < BEP+5). But the spec requires
                # the hover side to be WEAK (below BEP) at close of T itself.
                # This tightens the condition — Pattern B candles (close above BEP)
                # are correctly rejected here.
                # T weakness:  close < BEP  (same rule repeated at T+1 below)
                if hover_row['close'] >= hover_bep:
                    continue

                # Get hover side T+1 candle
                hover_next = get_next_candle(hover_idx, signal_dt) if hover_idx is not None else None
                if hover_next is None:
                    continue
                if hover_next.name.time() < MARKET_OPEN_FILTER:
                    continue

                # Hover side must still be below BEP at T+1 — not recovered
                if hover_next['close'] >= hover_bep:
                    continue

                # ── Check each breakout-side strike at T+1 ────────────────
                for bk_key, bk_df in self.candle_history.items():
                    if not bk_key.endswith(breakout_suffix):
                        continue
                    bk_bep = self.bep_data.get(bk_key)
                    if bk_bep is None or bk_df is None or bk_df.empty:
                        continue

                    bk_idx  = indexed.get(bk_key)
                    bk_next = get_next_candle(bk_idx, signal_dt) if bk_idx is not None else None
                    if bk_next is None:
                        continue
                    if bk_next.name.time() < MARKET_OPEN_FILTER:
                        continue

                    # T+1 sync check: breakout candle must be the SAME 5-min slot
                    # as hover_next — both sides must confirm on the identical candle.
                    # Without this, a CE in a downtrend can match a much later candle
                    # that happens to be above BEP, producing a false alert.
                    time_diff = abs(
                        (bk_next.name - hover_next.name)
                        .total_seconds()
                    )
                    if time_diff > 30:
                        continue

                    # Breakout confirmed: candle must have genuinely crossed BEP at T+1
                    #   low  <= BEP  — candle came from at or below BEP (touched it)
                    #   open >  BEP  — opened above BEP
                    #   close > BEP  — closed above BEP
                    # Without low <= BEP, a strike already floating well above BEP
                    # (never interacting with it) would falsely qualify.
                    # Example: 23350CE T+1 L:165.8 vs BEP:164.65 → low never
                    # touched BEP → correctly rejected.
                    if (bk_next['low']   <= bk_bep and
                            bk_next['open']  >  bk_bep and
                            bk_next['close'] >  bk_bep):
                        hover_strike = int(hover_key.split('_')[0])
                        bk_strike    = int(bk_key.split('_')[0])
                        results.append({
                            'action':          action,
                            'hover_time':      signal_dt.strftime('%H:%M'),
                            'confirm_time':    bk_next.name.strftime('%H:%M'),
                            'hover_key':       hover_key,
                            'hover_strike':    hover_strike,
                            'hover_opt':       'CE' if is_ce_hover else 'PE',
                            'hover_bep':       hover_bep,
                            'hover_open':      hover_row['open'],
                            'hover_high':      hover_row['high'],
                            'hover_low':       hover_row['low'],
                            'hover_close':     hover_row['close'],
                            'hover_close_T1':  hover_next['close'],
                            'breakout_key':    bk_key,
                            'breakout_strike': bk_strike,
                            'breakout_opt':    'PE' if is_ce_hover else 'CE',
                            'breakout_bep':    bk_bep,
                            'breakout_open':   bk_next['open'],
                            'breakout_close':  bk_next['close'],
                            'breakout_low':    bk_next['low'],
                            'breakout_high':   bk_next['high'],
                        })

        return results

    # ------------------------------------------------------------------
    # LIVE INCREMENTAL SCAN
    # Only checks the latest CLOSED 5-min candle — ~30 sec vs 3 min full scan
    # ------------------------------------------------------------------
    def scan_latest_candle(self) -> Tuple[List[Signal], List[str]]:
        new_signals: List[Signal] = []
        errors: List[str] = []
        if not self.bep_data:
            return new_signals, ["BEP data not calculated."]

        existing_ids = {
            f"{s.strike}_{s.option_type}_{s.candle_time.strftime('%H:%M')}"
            for s in self.signals
        }

        now = datetime.now(IST)
        minutes_since_open = (now.hour * 60 + now.minute) - (9 * 60 + 15)
        if minutes_since_open < 5:
            return new_signals, ["Market just opened — waiting for first full candle"]
        last_closed_minute = (minutes_since_open // 5) * 5 - 5
        candle_open = now.replace(
            hour=9, minute=15, second=0, microsecond=0
        ) + timedelta(minutes=last_closed_minute)
        candle_close_time = candle_open + timedelta(minutes=5)

        strikes = self._strikes
        progress = st.progress(0)
        total = len(strikes) * 2
        processed = 0

        for strike in strikes:
            for opt in ["CE", "PE"]:
                key = f"{strike}_{opt}"
                bep = self.bep_data.get(key)
                if not bep:
                    processed += 1
                    continue
                inst_key, _ = self.get_instrument_key(strike, opt)
                if not inst_key:
                    errors.append(f"{key}: No instrument key")
                    processed += 1
                    continue
                df, error = self.fetch_intraday_candles(inst_key)
                if df is None or df.empty:
                    errors.append(f"{key}: {error}")
                    processed += 1
                    time.sleep(0.2)
                    continue
                self.candle_history[key] = df
                closed = df[df["timestamp"] <= candle_close_time]
                if not closed.empty:
                    latest = closed.iloc[-1]
                    if abs((latest["timestamp"] - candle_open).total_seconds()) <= 300:
                        sigs = self.detect_rejection(
                            pd.DataFrame([latest]), bep, opt, strike
                        )
                        for sig in sigs:
                            sid = (f"{sig.strike}_{sig.option_type}_"
                                   f"{sig.candle_time.strftime('%H:%M')}")
                            if sid not in existing_ids:
                                new_signals.append(sig)
                                existing_ids.add(sid)
                processed += 1
                progress.progress(min(processed / total, 0.99))
                time.sleep(0.2)

        progress.empty()
        self.signals.extend(new_signals)
        return new_signals, errors


# ==========================================================
# HELPER FUNCTIONS
# ==========================================================

def get_next_expiry_date() -> date:
    """
    Nifty expires every Tuesday.
    - If today is Tuesday and market not yet closed (< 15:30) → return today
    - If today is Tuesday and market closed → return next Tuesday
    - Otherwise → return the coming Tuesday
    """
    today = datetime.now().date()
    now   = datetime.now()
    days_until_tue = (1 - today.weekday()) % 7   # Tuesday = weekday 1
    if days_until_tue == 0:
        # Today is Tuesday
        if now.hour < 15 or (now.hour == 15 and now.minute < 30):
            return today          # expiry day, market still open
        else:
            return today + timedelta(days=7)   # today's expiry passed
    return today + timedelta(days=days_until_tue)


def get_market_status() -> Tuple[str, str, int]:
    """
    Returns (status_label, color, seconds_to_next_candle_close)
    status: PRE-MARKET | LIVE | POST-MARKET | HOLIDAY
    """
    now = datetime.now(IST)
    if now.weekday() >= 5:
        return "HOLIDAY/WEEKEND", "#888", 0
    market_open  = now.replace(hour=9,  minute=15, second=0, microsecond=0)
    market_close = now.replace(hour=15, minute=30, second=0, microsecond=0)
    if now < market_open:
        return "PRE-MARKET", "#ffc107", 0
    elif now > market_close:
        return "POST-MARKET", "#888", 0
    else:
        # Seconds until the next 5-min candle closes
        elapsed = (now - market_open).seconds
        secs_in_candle = elapsed % 300
        secs_remaining = 300 - secs_in_candle
        return "LIVE 🟢", "#26a69a", secs_remaining


def generate_demo_bep_table(atm_strike: int, strike_range: int) -> pd.DataFrame:
    rows = []
    base_ce, base_pe = 146.15, 129.55
    for offset in range(-strike_range, strike_range + 1):
        strike = atm_strike + offset * 50
        ce_val = base_ce - offset * 35 + np.random.randn() * 2
        pe_val = base_pe + offset * 35 + np.random.randn() * 2
        rows.append({'Strike': strike,
                     'CE PDC': round(ce_val, 2),
                     'PE PDC': round(pe_val, 2),
                     'BEP': round((ce_val + pe_val) / 2, 2)})
    return pd.DataFrame(rows)


def generate_demo_signals(atm_strike: int) -> List[Signal]:
    base = datetime.now(IST).replace(hour=13, minute=40, second=0, microsecond=0)
    return [
        # CE support rejection (same as Image 3 left panel)
        Signal(atm_strike - 50, 'CE', 140.15, base,
               138.0, 145.0, 135.0, 142.0,
               'SUPPORT', 135.0, 145.0, 138.0, 142.0),
        # PE support rejection (same as Image 3 right panel)
        Signal(atm_strike, 'PE', 137.85, base,
               145.0, 150.0, 130.0, 140.0,
               'SUPPORT', 130.0, 150.0, 140.0, 145.0),
        # CE resistance at later candle
        Signal(atm_strike + 50, 'CE', 143.0, base + timedelta(minutes=35),
               150.0, 155.0, 145.0, 147.0,
               'RESISTANCE', 145.0, 155.0, 147.0, 150.0),
    ]


def render_chart(df: pd.DataFrame, bep: float, signals: List[Signal], title: str):
    fig = make_subplots(rows=1, cols=1)
    fig.add_trace(go.Candlestick(
        x=df['timestamp'], open=df['open'], high=df['high'],
        low=df['low'], close=df['close'],
        increasing_line_color='#26a69a', decreasing_line_color='#ef5350',
        name='5min'
    ))
    fig.add_hline(y=bep, line_dash="dash", line_color="purple",
                  annotation_text=f"BEP: {bep:.2f}", annotation_position="right")
    for sig in signals:
        color  = '#26a69a' if sig.signal_type == 'SUPPORT' else '#ef5350'
        symbol = 'triangle-up' if sig.signal_type == 'SUPPORT' else 'triangle-down'
        y_pos  = sig.low if sig.signal_type == 'SUPPORT' else sig.high
        fig.add_trace(go.Scatter(
            x=[sig.candle_time], y=[y_pos], mode='markers+text',
            marker=dict(size=16, color=color, symbol=symbol,
                        line=dict(width=2, color='white')),
            text=[sig.signal_type[:3]],
            textposition="top center" if sig.signal_type == 'SUPPORT' else "bottom center",
            textfont=dict(size=9, color=color), showlegend=False
        ))
    fig.update_layout(title=title, height=450, template='plotly_dark',
                      xaxis_rangeslider_visible=False)
    return fig


def style_bep_table(df: pd.DataFrame, atm_strike: int,
                    signal_strikes: Optional[set] = None):
    signal_strikes = signal_strikes or set()

    def highlight_row(row):
        if row['Strike'] == atm_strike:
            return ['background-color:#ffd700;color:#000;font-weight:bold'] * len(row)
        if row['Strike'] in signal_strikes:
            return ['background-color:rgba(38,166,154,0.35);font-weight:bold'] * len(row)
        return [''] * len(row)

    return df.style.apply(highlight_row, axis=1).format({
        'CE PDC': '{:.2f}', 'PE PDC': '{:.2f}', 'BEP': '{:.2f}'
    })


# ==========================================================
# NOTIFICATIONS  (browser Web API + in-app toast)
# ==========================================================

def inject_browser_notification_js():
    """Request browser notification permission once on app load."""
    st.components.v1.html("""
    <script>
    (function() {
        if (!('Notification' in window)) return;
        if (Notification.permission === 'default') {
            Notification.requestPermission();
        }
        window._bepNotify = function(title, body, tag) {
            if (Notification.permission !== 'granted') return;
            try {
                new Notification(title, {
                    body: body,
                    tag: tag || title,
                    icon: 'https://cdn-icons-png.flaticon.com/512/6295/6295417.png',
                    requireInteraction: false
                });
            } catch(e) { console.warn('BEP notify:', e); }
        };
    })();
    </script>
    """, height=0)


def browser_notify(title: str, body: str, tag: str = ""):
    esc = lambda s: s.replace("\\", "\\\\").replace("'", "\\'")
    st.components.v1.html(f"""
    <script>
    setTimeout(function() {{
        if (window._bepNotify) {{
            window._bepNotify('{esc(title)}', '{esc(body)}', '{esc(tag)}');
        }} else if ('Notification' in window && Notification.permission === 'granted') {{
            new Notification('{esc(title)}', {{body: '{esc(body)}', tag: '{esc(tag)}'}});
        }}
    }}, 350);
    </script>
    """, height=0)


def notify(title: str, body: str, level: str = "info",
           confluence: bool = False, tag: str = ""):
    icons = {"info": "ℹ️", "success": "🎯", "warning": "⚡", "error": "❌"}
    icon = icons.get(level, "ℹ️")
    try:
        st.toast(f"{icon} {title}: {body}")
    except Exception:
        st.info(f"{icon} {title}: {body}")
    browser_notify(f"{icon} {title}", body, tag=tag or title)
    if confluence:
        try:
            st.balloons()
        except Exception:
            pass


# ==========================================================
# TELEGRAM ALERTS
# ==========================================================

def _build_telegram_message(time_key: str, sigs: List[Signal]) -> str:
    """Build the confluence alert message text."""
    signal_lines = []
    for s in sigs:
        icon = "🟢" if s.signal_type == "SUPPORT" else "🔴"
        signal_lines.append(
            f"{icon} {s.strike} {s.option_type} | {s.signal_type} | BEP: {s.bep:.2f}\n"
            f"   O:{s.open:.1f} H:{s.high:.1f} L:{s.low:.1f} C:{s.close:.2f}"
        )
    hints = []
    for s in sigs:
        if s.signal_type == "SUPPORT":
            hints.append(f"• {s.strike}{s.option_type}: Entry > {s.bep:.2f} | SL < {s.wick_low:.1f}")
        else:
            hints.append(f"• {s.strike}{s.option_type}: Entry < {s.bep:.2f} | SL > {s.wick_high:.1f}")
    nl = "\n"
    return (
        f"⚡ *BEP CONFLUENCE ALERT*\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"🕐 *Candle Time:* {time_key}\n"
        f"📊 *Signals ({len(sigs)}):*\n"
        f"{nl.join(signal_lines)}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"📌 *Trade Hints:*\n"
        f"{nl.join(hints)}"
    )


def _send_to_one(bot_token: str, chat_id: str, message: str) -> Tuple[bool, str]:
    """Send a message to a single chat ID. Returns (success, error)."""
    url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
    try:
        resp = requests.post(
            url,
            json={"chat_id": chat_id.strip(), "text": message, "parse_mode": "Markdown"},
            timeout=10
        )
        if resp.status_code == 200 and resp.json().get("ok"):
            return True, ""
        err = resp.json().get("description", resp.text[:100])
        return False, f"Chat {chat_id.strip()}: {err}"
    except Exception as e:
        return False, f"Chat {chat_id.strip()}: {str(e)[:80]}"


def send_telegram_alert(bot_token: str, chat_ids_str: str,
                        time_key: str, sigs: List[Signal]) -> Tuple[bool, List[str]]:
    """
    Send confluence alert to ALL chat IDs (comma-separated string).
    Returns (all_success, list_of_errors).
    Each chat ID is tried independently — one failure does not block others.
    """
    if not bot_token or not chat_ids_str:
        return False, ["Bot token or Chat IDs not configured"]

    chat_ids = [c.strip() for c in chat_ids_str.split(",") if c.strip()]
    if not chat_ids:
        return False, ["No valid Chat IDs found"]

    message = _build_telegram_message(time_key, sigs)
    errors = []
    for cid in chat_ids:
        ok, err = _send_to_one(bot_token, cid, message)
        if not ok:
            errors.append(err)

    return len(errors) == 0, errors


def _build_breakout_telegram_message(breakout: Dict) -> str:
    """Build Telegram message for BEP BREAKOUT ALERT."""
    action        = breakout['action']            # 'BUY CE' or 'BUY PE'
    hover_time    = breakout['hover_time']        # candle T time
    conf_time     = breakout['confirm_time']      # candle T+1 time
    # Hover side (the side that stayed below BEP)
    hover_strike  = breakout['hover_strike']
    hover_opt     = breakout['hover_opt']
    hover_bep     = breakout['hover_bep']
    hover_open    = breakout['hover_open']
    hover_high    = breakout['hover_high']
    hover_low     = breakout['hover_low']
    hover_close   = breakout['hover_close']
    hover_close_T1 = breakout['hover_close_T1']
    # Breakout side
    bk_strike     = breakout['breakout_strike']
    bk_opt        = breakout['breakout_opt']
    bk_bep        = breakout['breakout_bep']
    bk_open       = breakout['breakout_open']
    bk_close      = breakout['breakout_close']
    bk_low        = breakout['breakout_low']
    bk_high       = breakout['breakout_high']

    return (
        f"🚀 *BEP BREAKOUT ALERT — 🟢 {action}*\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"🕐 *Hover candle (T):* {hover_time}\n"
        f"✅ *Breakout confirmed (T+1):* {conf_time}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"🔴 *Hover Side ({hover_opt}) — still below BEP at T & T+1:*\n"
        f"🔴 {hover_strike} {hover_opt} | BEP: {hover_bep:.2f}\n"
        f"   T  → O:{hover_open:.1f} H:{hover_high:.1f} L:{hover_low:.1f} C:{hover_close:.1f}\n"
        f"   T+1 → Close: {hover_close_T1:.1f} (below BEP ✅)\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"🟢 *Breakout Side ({bk_opt}) — confirmed above BEP at T+1:*\n"
        f"🟢 {bk_strike} {bk_opt} | BEP: {bk_bep:.2f}\n"
        f"   T+1 → O:{bk_open:.1f} H:{bk_high:.1f} L:{bk_low:.1f} C:{bk_close:.1f}\n"
        f"━━━━━━━━━━━━━━━━━━\n"
        f"📌 *Trade Hints:*\n"
        f"• 🟢 *{action}* {bk_strike}{bk_opt}: Entry > {bk_bep:.2f} | SL < {bk_low:.1f}"
    )


def send_breakout_telegram_alert(bot_token: str, chat_ids_str: str,
                                  breakout: Dict) -> Tuple[bool, List[str]]:
    """Send BEP BREAKOUT ALERT to all chat IDs."""
    if not bot_token or not chat_ids_str:
        return False, ["Bot token or Chat IDs not configured"]
    chat_ids = [c.strip() for c in chat_ids_str.split(",") if c.strip()]
    if not chat_ids:
        return False, ["No valid Chat IDs found"]
    message = _build_breakout_telegram_message(breakout)
    errors = []
    for cid in chat_ids:
        ok, err = _send_to_one(bot_token, cid, message)
        if not ok:
            errors.append(err)
    return len(errors) == 0, errors



def test_telegram_connection(bot_token: str, chat_ids_str: str) -> Tuple[bool, List[str]]:
    """
    Send a test message to ALL chat IDs to verify connection.
    Returns (all_success, list_of_errors).
    """
    if not bot_token or not chat_ids_str:
        return False, ["Bot token or Chat IDs is empty"]

    chat_ids = [c.strip() for c in chat_ids_str.split(",") if c.strip()]
    if not chat_ids:
        return False, ["No valid Chat IDs found"]

    test_msg = "✅ *BEP Scanner Pro* — Telegram alert connected successfully! Ready for confluence signals."
    errors = []
    for cid in chat_ids:
        ok, err = _send_to_one(bot_token, cid, test_msg)
        if not ok:
            errors.append(err)

    return len(errors) == 0, errors


# ==========================================================
# PERSISTENT SIGNAL LOG  (CSV on disk, survives restarts)
# ==========================================================

LOG_DIR  = os.path.join(os.path.expanduser("~"), "bep_logs")
os.makedirs(LOG_DIR, exist_ok=True)

def _log_path() -> str:
    """One CSV file per trading day."""
    return os.path.join(LOG_DIR, f"bep_signals_{datetime.now().strftime('%Y%m%d')}.csv")


def load_signal_log() -> pd.DataFrame:
    """Load today's signal log from disk. Returns empty DataFrame if none exists."""
    path = _log_path()
    if os.path.exists(path):
        try:
            return pd.read_csv(path)
        except Exception:
            pass
    return pd.DataFrame(columns=[
        'Date','Candle Time','Strike','Type','Signal','BEP',
        'Open','High','Low','Close','Wick Low','Wick High','Detected At'
    ])


def append_signals_to_log(signals: List[Signal], already_logged: set) -> set:
    """
    Append only NEW signals to the CSV log.
    already_logged: set of signal IDs logged this session (avoids double-write on rerun).
    Returns updated already_logged set.
    """
    path = _log_path()
    new_rows = []
    for sig in signals:
        sid = f"{sig.strike}_{sig.option_type}_{sig.candle_time.strftime('%Y%m%d_%H%M')}"
        if sid not in already_logged:
            already_logged.add(sid)
            new_rows.append(sig.to_dict(include_meta=True))
    if new_rows:
        df_new = pd.DataFrame(new_rows)
        write_header = not os.path.exists(path)
        df_new.to_csv(path, mode='a', header=write_header, index=False)
    return already_logged


def list_log_files() -> List[str]:
    """Return sorted list of all log files (newest first)."""
    files = sorted(
        [f for f in os.listdir(LOG_DIR) if f.startswith('bep_signals_') and f.endswith('.csv')],
        reverse=True
    )
    return files


# ==========================================================
# MAIN APP
# ==========================================================

def main():
    st.set_page_config(page_title="BEP Scanner Pro v4.3", layout="wide")
    inject_browser_notification_js()

    st.markdown("""
    <style>
    .main-title  {text-align:center;font-size:2.4rem;font-weight:bold;color:#00d4ff;}
    .sub-title   {text-align:center;font-size:1.1rem;color:#888;margin-bottom:1.5rem;}
    .conf-box    {background:rgba(255,215,0,.12);border:2px solid #ffd700;
                  border-radius:10px;padding:1rem;margin:.5rem 0;}
    .sig-support {background:rgba(38,166,154,.12);border-left:4px solid #26a69a;
                  border-radius:5px;padding:.8rem;margin:.3rem 0;}
    .sig-resist  {background:rgba(239,83,80,.12);border-left:4px solid #ef5350;
                  border-radius:5px;padding:.8rem;margin:.3rem 0;}
    .breakout-box {background:rgba(0,230,118,.10);border:2px solid #00e676;
                   border-radius:10px;padding:1rem;margin:.5rem 0;}
    .warn-box    {background:rgba(255,193,7,.15);border:1px solid #ffc107;
                  border-radius:5px;padding:1rem;margin:.5rem 0;color:#fff;}
    .notif-bar   {background:rgba(0,212,255,.08);border:1px solid #00d4ff;
                  border-radius:8px;padding:.6rem 1rem;margin:.5rem 0;
                  font-size:.85rem;color:#00d4ff;}
    </style>
    """, unsafe_allow_html=True)

    st.markdown('<div class="main-title">BEP BREAK-EVEN POINT SCANNER PRO v4.3</div>',
                unsafe_allow_html=True)
    st.markdown(
        '<div class="sub-title">Live instrument fetch · Expiry date picker · '
        'CE+PE dual rejection · Browser notifications</div>',
        unsafe_allow_html=True)

    # Session state defaults
    for k, v in [('notified_ids', set()), ('logged_signal_ids', set()),
                  ('bep_table', None), ('atm_strike', 23400),
                  ('prev_atm', None), ('prev_range', None), ('prev_expiry', None),
                  ('signals', []), ('beps_calculated', False),
                  ('notified_breakout_ids', set())]:
        if k not in st.session_state:
            st.session_state[k] = v

    st.markdown("""
    <div class="notif-bar">
    🔔 <b>Browser Notifications:</b> Click <b>Allow</b> when your browser asks for
    permission so you receive alerts even when this tab is in the background.
    </div>
    """, unsafe_allow_html=True)

    # ── SIDEBAR ──────────────────────────────────────────────────────────
    with st.sidebar:
        st.header("⚙️ Configuration")

        demo_mode = st.checkbox("Demo Mode (No API)", value=False,
                                help="Test the UI with simulated data — no token needed")

        # Expiry date picker
        default_expiry = get_next_expiry_date()
        selected_expiry: date = st.date_input(
            "📅 Expiry Date",
            value=default_expiry,
            min_value=datetime.now().date(),
            help="Nifty expires every Tuesday. Defaults to the nearest upcoming Tuesday expiry."
        )

        atm_strike = st.number_input("ATM Strike", value=st.session_state.atm_strike,
                                     step=50, min_value=10000, max_value=99950)

        strike_range = st.slider("Strike Range (±)", 1, 20, 5,
                                 help="Number of strikes above and below ATM to scan (±50pts each)")
        auto_refresh = st.checkbox("Live Auto-Scan (every 5 min)", value=False,
                                help="Scans only the latest closed 5-min candle. Works during market hours 9:15–15:30 IST")

        if not demo_mode:
            access_token = st.text_input(
                "🔑 Upstox Access Token", type="password",
                help="Paste your Upstox v3 API access token"
            )
        else:
            access_token = ""

        # Re-centre ATM button — placed after access_token so the token is always defined
        if not demo_mode:
            if st.button("🎯 Re-centre ATM", width='stretch',
                         help="Fetch live Nifty spot price and snap ATM to nearest 50"):
                if not access_token:
                    st.error("Enter Access Token first.")
                else:
                    with st.spinner("Fetching Nifty spot price…"):
                        _tmp = UpstoxBEPScanner(access_token, int(atm_strike), 1)
                        spot, err = _tmp.fetch_nifty_spot()
                    if spot:
                        new_atm = int(round(spot / 50) * 50)
                        st.session_state.atm_strike = new_atm
                        # Clear stale data so user must recalculate
                        st.session_state.signals           = []
                        st.session_state.notified_ids      = set()
                        st.session_state.logged_signal_ids = set()
                        st.session_state.bep_table         = None
                        st.session_state.beps_calculated   = False
                        if "scanner" in st.session_state:
                            del st.session_state["scanner"]
                        st.success(
                            f"Nifty spot: **{spot:.0f}** → ATM set to **{new_atm}**. "
                            f"Click Calculate BEPs to refresh."
                        )
                        st.rerun()
                    else:
                        st.error(f"Could not fetch spot: {err}")

        st.session_state.atm_strike = int(atm_strike)
        st.divider()

        # ── Telegram Configuration ────────────────────────────────
        st.subheader("📱 Telegram Alerts")
        tg_token = st.text_input(
            "🤖 Bot Token", type="password",
            key="tg_token",
            help="From @BotFather — looks like 7123456789:AAFxxx..."
        )
        tg_chat_ids = st.text_area(
            "💬 Chat IDs (one per line or comma separated)",
            value="5756696141, 7266173638",
            key="tg_chat_ids",
            height=80,
            help="Add multiple Chat IDs separated by commas or new lines"
        )
        tg_enabled = st.checkbox(
            "Enable Telegram Alerts", value=False,
            key="tg_enabled",
            help="Send confluence alerts to Telegram"
        )
        if st.button("📨 Test Telegram", width='stretch'):
            if not tg_token or not tg_chat_ids:
                st.error("Enter Bot Token and Chat IDs first.")
            else:
                # Normalise newlines to commas
                ids_str = tg_chat_ids.replace("\n", ",")
                with st.spinner("Sending test to all accounts…"):
                    ok, errs = test_telegram_connection(tg_token, ids_str)
                if ok:
                    ids_list = [c.strip() for c in ids_str.split(",") if c.strip()]
                    st.success(f"✅ Message sent to {len(ids_list)} account(s)! Check Telegram.")
                else:
                    for e in errs:
                        st.error(f"❌ {e}")

        st.divider()

        if st.button("🔔 Test Notification", width='stretch'):
            notify("Test Alert", "Browser + in-app notifications working!",
                   level="success", tag="test_notif")

        if not demo_mode and st.button("🧪 Test API Connection", width='stretch'):
            if not access_token:
                st.error("Enter Access Token first.")
            else:
                with st.spinner("Testing Upstox API…"):
                    test_scanner = UpstoxBEPScanner(
                        access_token, int(atm_strike), 1,
                        target_expiry=selected_expiry
                    )
                    st.write("**Step 1:** Instrument search…")
                    count, errs = test_scanner.fetch_instruments_from_api()
                    if count > 0:
                        st.success(f"✅ Found {count} instrument keys")
                        sample_key = list(test_scanner.instruments_lookup.values())[0]
                    else:
                        st.warning("⚠️ Search returned 0 — using direct key fallback")
                        sample_key = test_scanner._build_instrument_key_direct(int(atm_strike), 'CE')
                        if errs:
                            with st.expander("Search errors"):
                                st.write("\n".join(errs[:5]))
                    st.code(f"Key: {sample_key}")

                    st.write("**Step 2:** Previous Day Close…")
                    pdc, err = test_scanner.fetch_previous_day_close(sample_key)
                    if pdc:
                        st.success(f"✅ PDC = {pdc}")
                    else:
                        st.error(f"❌ PDC failed: {err}")

                    st.write("**Step 3:** Intraday 5-min candles…")
                    df_test, err2 = test_scanner.fetch_intraday_candles(sample_key)
                    if df_test is not None and not df_test.empty:
                        st.success(f"✅ {len(df_test)} candles loaded")
                        st.dataframe(df_test.tail(3), width='stretch')
                    else:
                        st.error(f"❌ Intraday failed: {err2}")
                        st.caption("Intraday is empty outside market hours 9:15–15:30 IST")

                    if hasattr(test_scanner, 'debug_sample') and test_scanner.debug_sample:
                        with st.expander("🔍 Raw API instrument sample"):
                            st.json(test_scanner.debug_sample)

        # Calculate BEPs
        if st.button("📊 Calculate BEPs", type="primary", width='stretch'):
            # ── Reset all stale state when ATM / range / expiry changes ──
            config_changed = (
                st.session_state.prev_atm    != int(atm_strike) or
                st.session_state.prev_range  != strike_range or
                st.session_state.prev_expiry != str(selected_expiry)
            )
            if config_changed:
                st.session_state.signals          = []
                st.session_state.notified_ids     = set()
                st.session_state.logged_signal_ids = set()
                st.session_state.bep_table        = None
                st.session_state.beps_calculated  = False
                if 'scanner' in st.session_state:
                    del st.session_state['scanner']

            # Record current config
            st.session_state.prev_atm    = int(atm_strike)
            st.session_state.prev_range  = strike_range
            st.session_state.prev_expiry = str(selected_expiry)

            if demo_mode:
                st.session_state.bep_table = generate_demo_bep_table(int(atm_strike), strike_range)
                st.session_state.beps_calculated = True
                st.success("Demo BEPs ready!")
            else:
                if not access_token:
                    st.error("Enter your Upstox Access Token first.")
                else:
                    try:
                        scanner = UpstoxBEPScanner(
                            access_token, int(atm_strike), strike_range,
                            target_expiry=selected_expiry
                        )
                        with st.spinner(
                            f"Fetching instruments for "
                            f"{selected_expiry.strftime('%d %b %Y')} from Upstox API…"
                        ):
                            count, inst_errors = scanner.fetch_instruments_from_api()

                        if count == 0:
                            st.markdown(f"""
                            <div class="warn-box">
                            <b>No instruments found for {selected_expiry.strftime('%d %b %Y')}!</b><br>
                            • Verify the expiry date against NSE calendar<br>
                            • Check your access token is valid<br>
                            • Falling back to direct key construction
                            </div>
                            """, unsafe_allow_html=True)
                            # Show raw API sample to diagnose field names
                            if hasattr(scanner, 'debug_sample') and scanner.debug_sample:
                                with st.expander("🔍 Raw API Response Sample (debug)"):
                                    st.json(scanner.debug_sample)
                        else:
                            st.success(f"✅ Loaded {count} instruments for "
                                       f"{selected_expiry.strftime('%d %b %Y')}")

                        if inst_errors:
                            with st.expander(f"Instrument warnings ({len(inst_errors)})"):
                                for e in inst_errors[:30]:
                                    st.text(e)

                        with st.spinner("Fetching Previous Day Close (PDC)…"):
                            bep_df, errors = scanner.calculate_all_beps()

                        st.session_state.scanner = scanner
                        st.session_state.bep_table = bep_df
                        st.session_state.bep_errors = errors
                        st.session_state.beps_calculated = True

                        if len(bep_df) > 0:
                            st.success(f"BEPs calculated for {len(bep_df)} strikes")
                        else:
                            st.error("No BEPs calculated. Check token & expiry date.")

                        if errors:
                            with st.expander(f"PDC errors ({len(errors)})"):
                                for e in errors[:20]:
                                    st.text(e)

                    except Exception as ex:
                        st.error(f"Failed: {ex}")

        # Scan Signals
        if st.button("🔍 Scan Signals", type="secondary", width='stretch'):
            if demo_mode:
                signals = generate_demo_signals(int(atm_strike))
                st.session_state.signals = signals
                st.session_state.last_scan = datetime.now()
                st.session_state.demo_candles = {}
                for sig in signals:
                    key = f"{sig.strike}_{sig.option_type}"
                    times = pd.date_range(
                        start=datetime.now(IST).replace(hour=9, minute=15),
                        periods=75, freq='5min'
                    )
                    base = sig.bep + np.random.randn(75).cumsum() * 2
                    df = pd.DataFrame({
                        'timestamp': times,
                        'open': base, 'high': base + 2,
                        'low': base - 2, 'close': base + 1,
                        'volume': np.random.randint(1000, 5000, 75),
                        'oi': np.random.randint(10000, 50000, 75)
                    })
                    idx = 42
                    df.loc[idx, ['low','high','open','close']] = [
                        sig.wick_low, sig.wick_high, sig.open, sig.close]
                    st.session_state.demo_candles[key] = df
                st.success(f"Demo signals: {len(signals)}")
            else:
                if 'scanner' not in st.session_state:
                    st.error("Calculate BEPs first!")
                else:
                    try:
                        scanner = st.session_state.scanner
                        with st.spinner("Scanning 5-min candles via Upstox v3 API…"):
                            signals, errors = scanner.scan_all_strikes()
                        st.session_state.signals = signals
                        st.session_state.scan_errors = errors
                        st.session_state.last_scan = datetime.now()
                        st.success(f"Signals found: {len(signals)}")
                        if errors:
                            with st.expander(f"Scan errors ({len(errors)})"):
                                for e in errors[:20]:
                                    st.text(e)
                        # Force a clean rerun so the signals table, metrics, and
                        # confluence logic all read the freshly stored session state.
                        # Without this, signal_count and grouped2 are computed from
                        # the OLD session state in the same Streamlit execution pass.
                        st.rerun()
                    except Exception as ex:
                        st.error(f"Scan failed: {ex}")

    # ── Fire notifications — two-stage confluence ──────────────────────
    if st.session_state.signals:
        # Initialise notified sets if missing
        if 'notified_wait_ids' not in st.session_state:
            st.session_state.notified_wait_ids = set()
        if 'notified_confirmed_ids' not in st.session_state:
            st.session_state.notified_confirmed_ids = set()

        tg_token    = st.session_state.get("tg_token", "")
        tg_chat_ids = st.session_state.get("tg_chat_ids", "")
        tg_enabled  = st.session_state.get("tg_enabled", False)
        tg_ids_str  = tg_chat_ids.replace("\n", ",") if tg_chat_ids else ""

        if not demo_mode and 'scanner' in st.session_state:
            scanner_obj = st.session_state.scanner

            # Compute once and cache — these are reused in the metrics/UI block below.
            # Calling them twice per rerun (here + metrics) wastes CPU on iterrows loops.
            potential       = scanner_obj.get_confluence_signals()
            confirmed_map   = scanner_obj.confirm_confluence()
            breakout_alerts = scanner_obj.detect_bep_breakout()
            st.session_state['_cached_potential']       = potential
            st.session_state['_cached_confirmed_map']   = confirmed_map
            st.session_state['_cached_breakout_alerts'] = breakout_alerts
            for time_key, sigs in potential.items():
                wid = f"wait_{time_key}"
                if wid not in st.session_state.notified_wait_ids:
                    st.session_state.notified_wait_ids.add(wid)
                    detail = ' | '.join(
                        f"{s.strike}{s.option_type}({s.signal_type[0]})" for s in sigs)
                    notify("⏳ WAIT — Potential Confluence",
                           f"{time_key}: {detail}", level="info", tag=wid)
                    if tg_enabled and tg_token and tg_ids_str:
                        wait_msg = (
                            f"⏳ *WAIT — Potential Confluence*\n"
                            f"🕐 Signal candle: {time_key}\n"
                            f"{detail}\n"
                            f"_Awaiting confirmation (up to 4 candles)…_"
                        )
                        for cid in [c.strip() for c in tg_ids_str.split(",") if c.strip()]:
                            requests.post(
                                f"https://api.telegram.org/bot{tg_token}/sendMessage",
                                json={"chat_id": cid, "text": wait_msg, "parse_mode": "Markdown"},
                                timeout=10
                            )

            # Stage 2 — BUY / SELL confirmed alerts
            for time_key, result in confirmed_map.items():
                if result['status'] != 'CONFIRMED':
                    continue
                cid_key = f"confirmed_{time_key}"
                if cid_key not in st.session_state.notified_confirmed_ids:
                    st.session_state.notified_confirmed_ids.add(cid_key)
                    action = result['action']
                    conf_t = result['confirm_time']
                    sigs   = result['sigs']
                    detail = ' | '.join(
                        f"{s.strike}{s.option_type}({s.signal_type[0]})" for s in sigs)
                    level  = "success" if action == 'BUY' else "warning"
                    notify(f"✅ {action} — Confluence Confirmed",
                           f"Signal:{time_key} → Confirmed:{conf_t} | {detail}",
                           level=level, confluence=True, tag=cid_key)
                    if tg_enabled and tg_token and tg_ids_str:
                        tg_ok, tg_errs = send_telegram_alert(
                            tg_token, tg_ids_str, conf_t or time_key, sigs
                        )
                        if not tg_ok:
                            for e in tg_errs:
                                st.warning(f"⚠️ Telegram failed: {e}")

            # BEP BREAKOUT ALERT — v3.15
            for bk in breakout_alerts:
                # Dedup key: one alert per breakout candle (action + confirm_time + strike + opt)
                bk_id = (f"breakout_{bk['action']}_{bk['confirm_time']}_"
                         f"{bk['breakout_strike']}{bk['breakout_opt']}")
                if bk_id not in st.session_state.notified_breakout_ids:
                    st.session_state.notified_breakout_ids.add(bk_id)
                    notify(
                        f"🚀 BEP BREAKOUT — 🟢 {bk['action']}",
                        f"Hover: {bk['hover_time']} → Breakout: {bk['confirm_time']} "
                        f"| {bk['breakout_strike']}{bk['breakout_opt']} broke BEP {bk['breakout_bep']:.2f}",
                        level="success", confluence=True,
                        tag=bk_id
                    )
                    if tg_enabled and tg_token and tg_ids_str:
                        bk_ok, bk_errs = send_breakout_telegram_alert(
                            tg_token, tg_ids_str, bk
                        )
                        if not bk_ok:
                            for e in bk_errs:
                                st.warning(f"⚠️ Breakout Telegram failed: {e}")

    # ── Stale config warning ───────────────────────────────────────────
    if st.session_state.beps_calculated:
        stale = (
            st.session_state.prev_atm    != int(atm_strike) or
            st.session_state.prev_range  != strike_range or
            st.session_state.prev_expiry != str(selected_expiry)
        )
        if stale:
            st.warning(
                f"⚠️ **Config changed!** BEP table is for ATM={st.session_state.prev_atm} "
                f"Range=±{st.session_state.prev_range} "
                f"Expiry={st.session_state.prev_expiry}. "
                f"Click **Calculate BEPs** again to refresh for new settings."
            )

    # ── BEP TABLE ──────────────────────────────────────────────────────
    if st.session_state.bep_table is not None:
        st.subheader("📋 BEP Reference Table")
        st.caption(
            f"BEP = (CE PDC + PE PDC) / 2  ·  "
            f"Expiry: {selected_expiry.strftime('%d %b %Y')}  ·  "
            f"ATM {st.session_state.atm_strike} = gold  ·  Signal strikes = green"
        )
        bep_df = st.session_state.bep_table.copy()
        signal_strikes = set(s.strike for s in st.session_state.signals)

        if len(bep_df) > 0:
            styled = style_bep_table(bep_df, st.session_state.atm_strike, signal_strikes)
            st.dataframe(styled, width='stretch', height=500, hide_index=True)
            st.download_button("⬇️ Download BEP Table",
                               bep_df.to_csv(index=False), "bep_table.csv", "text/csv")
        else:
            st.error("No BEP data available.")

        if 'bep_errors' in st.session_state and st.session_state.bep_errors:
            with st.expander(f"API Errors ({len(st.session_state.bep_errors)})"):
                for e in st.session_state.bep_errors[:20]:
                    st.text(e)
        st.divider()

    # ── METRICS ────────────────────────────────────────────────────────
    # IMPORTANT: always re-read signals from session_state here — never
    # cache signal_count before this point. The scan button updates
    # st.session_state.signals earlier in the same Streamlit run, and if
    # signal_count was captured before the button logic executed it would
    # be 0, leaving grouped2/confirmed_map2 empty and the table stale
    # until the next manual rerun.
    # Use the cached results computed in the notification block above —
    # get_confluence_signals / confirm_confluence / detect_bep_breakout are
    # O(n*candles) loops; calling them 3× per rerun (notify + metrics + UI)
    # is wasteful. The cache is set in the notification block above.
    c1, c2, c3, c4, c5 = st.columns(5)
    signal_count = len(st.session_state.signals)   # always fresh from session state
    grouped2: Dict[str, List[Signal]]  = st.session_state.get('_cached_potential', {})
    confirmed_map2: Dict[str, Dict]    = st.session_state.get('_cached_confirmed_map', {})
    breakout_alerts2: List[Dict]       = st.session_state.get('_cached_breakout_alerts', [])
    # Demo mode: compute fresh (no cache set for demo)
    if signal_count > 0 and demo_mode:
        grouped2 = {}  # demo has no scanner object
    confirmed_count  = sum(1 for r in confirmed_map2.values() if r['status'] == 'CONFIRMED')
    pending_count    = sum(1 for r in confirmed_map2.values() if r['status'] == 'PENDING')
    confluence_count = len(grouped2)

    c1.metric("ATM Strike", st.session_state.atm_strike)
    c2.metric("Expiry", selected_expiry.strftime('%d %b %Y'))
    c3.metric("Raw Signals", signal_count)
    c4.metric("Potential Confluence", confluence_count)
    c5.metric("Confirmed Signals", confirmed_count,
              f"{pending_count} pending" if pending_count > 0 else None)
    if breakout_alerts2:
        st.markdown(
            f"<div style='background:rgba(0,230,118,.12);border:1px solid #00e676;"
            f"border-radius:8px;padding:.5rem 1rem;margin:.3rem 0;display:inline-block;'>"
            f"🚀 <b style='color:#00e676;'>BEP BREAKOUT ALERTS: {len(breakout_alerts2)}</b>"
            f"</div>",
            unsafe_allow_html=True
        )

    if 'last_scan' in st.session_state:
        st.caption(f"Last scan: {st.session_state.last_scan.strftime('%H:%M:%S')}")
    st.divider()

    # ── CONFLUENCE ALERTS — two-stage display ──────────────────────────
    if signal_count > 0 and grouped2:
        st.subheader("⚡ Confluence Alerts")

        # ── Stage 2: Confirmed BUY / SELL ──────────────────────────────
        confirmed_items = {k: v for k, v in confirmed_map2.items()
                           if v['status'] == 'CONFIRMED'}
        if confirmed_items:
            st.markdown("### ✅ Confirmed Signals")
            for time_key, result in confirmed_items.items():
                action    = result['action']
                conf_time = result['confirm_time']
                sigs      = result['sigs']
                color     = '#26a69a' if action == 'BUY' else '#ef5350'
                rows_html = "<br>".join([
                    f"<span style='color:"
                    f"{'#26a69a' if s.signal_type == 'SUPPORT' else '#ef5350'}'>"
                    f"• {s.strike} {s.option_type} ({s.signal_type}) BEP:{s.bep:.2f}</span>"
                    for s in sigs
                ])
                st.markdown(f"""
                <div style="background:rgba({"38,166,154" if action=="BUY" else "239,83,80"},.15);
                            border:2px solid {color};border-radius:10px;
                            padding:1rem;margin:.5rem 0;">
                    <b style="color:{color};font-size:1.2rem;">
                        {"🟢" if action=="BUY" else "🔴"} {action} SIGNAL
                    </b><br>
                    <small>Signal candle: <b>{time_key}</b> → Confirmed: <b>{conf_time}</b></small>
                    <br>{rows_html}
                </div>
                """, unsafe_allow_html=True)

        # ── Stage 1: WAIT (potential, not yet confirmed) ────────────────
        wait_items = {k: v for k, v in confirmed_map2.items()
                      if v['status'] == 'PENDING'}
        # Also show potential ones not yet in confirmed_map2 (no candle history yet)
        for tk, sigs in grouped2.items():
            if tk not in confirmed_map2:
                wait_items[tk] = {'signal_time': tk, 'sigs': sigs,
                                  'status': 'PENDING', 'action': None, 'confirm_time': None}

        if wait_items:
            st.markdown("### ⏳ Waiting for Confirmation")
            for time_key, result in wait_items.items():
                sigs      = result['sigs']
                rows_html = "<br>".join([
                    f"<span style='color:"
                    f"{'#26a69a' if s.signal_type == 'SUPPORT' else '#ef5350'}'>"
                    f"• {s.strike} {s.option_type} ({s.signal_type}) BEP:{s.bep:.2f}</span>"
                    for s in sigs
                ])
                st.markdown(f"""
                <div class="conf-box">
                    <b>⏳ WAIT</b> | Signal candle: <b>{time_key}</b>
                    | Awaiting confirmation (up to 4 candles)<br>{rows_html}
                </div>
                """, unsafe_allow_html=True)

        # ── Invalidated (collapsed) ─────────────────────────────────────
        invalid_items = {k: v for k, v in confirmed_map2.items()
                         if v['status'] == 'INVALIDATED'}
        if invalid_items:
            with st.expander(f"❌ Invalidated ({len(invalid_items)})"):
                for time_key, result in invalid_items.items():
                    sigs = result['sigs']
                    detail = ' | '.join(
                        f"{s.strike}{s.option_type}({s.signal_type[0]})" for s in sigs)
                    st.markdown(f"**{time_key}** — {detail} _(resistance broke above BEP)_")

    # ── BEP BREAKOUT ALERTS (v3.15) ────────────────────────────────────
    if breakout_alerts2:
        st.markdown("### 🚀 BEP Breakout Alerts")
        for bk in breakout_alerts2:
            action      = bk['action']
            hover_time  = bk['hover_time']
            conf_time   = bk['confirm_time']
            hover_strike = bk['hover_strike']
            hover_opt   = bk['hover_opt']
            hover_bep   = bk['hover_bep']
            hover_open  = bk['hover_open']
            hover_high  = bk['hover_high']
            hover_low   = bk['hover_low']
            hover_close = bk['hover_close']
            hover_close_T1 = bk['hover_close_T1']
            bk_strike   = bk['breakout_strike']
            bk_opt      = bk['breakout_opt']
            bk_bep      = bk['breakout_bep']
            bk_open     = bk['breakout_open']
            bk_close    = bk['breakout_close']
            bk_low      = bk['breakout_low']
            bk_high     = bk['breakout_high']
            with st.expander(
                f"🚀 BEP BREAKOUT ALERT — 🟢 {action} "
                f"| Hover: {hover_time} → Breakout: {conf_time} "
                f"| {bk_strike}{bk_opt} broke BEP {bk_bep:.2f}",
                expanded=True
            ):
                st.markdown(f"""
                <div class="breakout-box">
                    <b style="color:#00e676;font-size:1.2rem;">
                        🚀 BEP BREAKOUT ALERT &nbsp;|&nbsp; 🟢 {action}
                    </b><br>
                    <small>
                        Hover candle (T): <b>{hover_time}</b>
                        &nbsp;→&nbsp; Breakout confirmed (T+1): <b>{conf_time}</b>
                    </small>
                    <br><br>
                    <span style="color:#ef5350;">
                        🔴 Hover side: {hover_strike} {hover_opt}
                        | BEP: {hover_bep:.2f}
                        | T → O:{hover_open:.1f} H:{hover_high:.1f}
                        L:{hover_low:.1f} C:{hover_close:.1f}
                        | T+1 Close: {hover_close_T1:.1f} (below BEP ✅)
                    </span><br>
                    <span style="color:#00e676;">
                        🟢 Breakout: {bk_strike} {bk_opt}
                        | BEP: {bk_bep:.2f}
                        | T+1 → O:{bk_open:.1f} H:{bk_high:.1f}
                        L:{bk_low:.1f} C:{bk_close:.1f}
                    </span><br><br>
                    <b>📌 Trade Hints:</b><br>
                    <span style="color:#00e676;">
                        • 🟢 {action} {bk_strike}{bk_opt}:
                        Entry &gt; {bk_bep:.2f} &nbsp;|&nbsp;
                        SL &lt; {bk_low:.1f}
                    </span>
                </div>
                """, unsafe_allow_html=True)

    # ── ALL SIGNALS TABLE ──────────────────────────────────────────────
    all_signals = st.session_state.signals
    if all_signals:
        st.subheader("📈 BEP Signals")
        # Build set of signal ids that belong to a confluence group
        confluence_ids = {
            f"{s.strike}_{s.option_type}_{s.candle_time.strftime('%H:%M')}"
            for sigs in grouped2.values() for s in sigs
        }
        rows = []
        for s in all_signals:
            d = s.to_dict()
            sid = f"{s.strike}_{s.option_type}_{s.candle_time.strftime('%H:%M')}"
            d['Confluence'] = 'Yes' if sid in confluence_ids else 'No'
            rows.append(d)
        df_sig = pd.DataFrame(rows)
        # Reorder so Confluence column appears after Signal
        cols = df_sig.columns.tolist()
        if 'Signal' in cols and 'Confluence' in cols:
            cols.remove('Confluence')
            idx = cols.index('Signal') + 1
            cols.insert(idx, 'Confluence')
            df_sig = df_sig[cols]
        df_sig = df_sig.sort_values('Candle Time', ascending=False)

        def highlight_signal(row):
            if row.get('Confluence') == 'Yes':
                if row['Signal'] == 'SUPPORT':
                    return ['background:rgba(38,166,154,0.35)'] * len(row)
                return ['background:rgba(239,83,80,0.35)'] * len(row)
            if row['Signal'] == 'SUPPORT':
                return ['background:rgba(38,166,154,0.12)'] * len(row)
            return ['background:rgba(239,83,80,0.12)'] * len(row)

        st.dataframe(df_sig.style.apply(highlight_signal, axis=1),
                     width='stretch', height=350)
        st.download_button("⬇️ Download BEP Signals CSV",
                           df_sig.to_csv(index=False), "bep_signals.csv", "text/csv")

    # ── RAW CANDLE DEBUG VIEWER ────────────────────────────────────────
    # Lets you inspect exactly what Upstox API returned for any strike+candle,
    # so you can compare against TradingView and diagnose missing signals.
    st.divider()
    if not demo_mode and 'scanner' in st.session_state:
        with st.expander("🔬 Raw Candle Debug — Compare API data vs TradingView", expanded=False):
            scanner_dbg = st.session_state.scanner
            candle_keys = sorted(scanner_dbg.candle_history.keys())

            if not candle_keys:
                st.info("No candle data loaded yet. Run 'Scan Signals' first.")
            else:
                st.caption(
                    "Select a strike to see every 5-min candle the API returned. "
                    "Compare OHLC values against TradingView to spot discrepancies. "
                    "Also shows which candles passed/failed each signal rule."
                )

                col_sel1, col_sel2 = st.columns([2, 1])
                with col_sel1:
                    selected_key = st.selectbox(
                        "Strike / Option",
                        candle_keys,
                        format_func=lambda k: k.replace('_', ' '),
                        key="dbg_strike_select"
                    )
                with col_sel2:
                    show_rule_check = st.checkbox(
                        "Show rule breakdown", value=True,
                        key="dbg_show_rules",
                        help="For each candle show exactly which SUPPORT/RESISTANCE rules passed or failed"
                    )

                df_raw = scanner_dbg.candle_history.get(selected_key)
                bep_val = scanner_dbg.bep_data.get(selected_key)

                if df_raw is None or df_raw.empty:
                    st.warning(f"No candle data found for {selected_key}")
                else:
                    st.markdown(
                        f"**{selected_key.replace('_', ' ')}** | "
                        f"BEP: **{bep_val:.2f}** | "
                        f"Total candles: **{len(df_raw)}** | "
                        f"Range: {df_raw['timestamp'].iloc[0].strftime('%H:%M')} "
                        f"→ {df_raw['timestamp'].iloc[-1].strftime('%H:%M')}"
                    )

                    # Build display dataframe
                    display_rows = []
                    for _, row in df_raw.iterrows():
                        o, h, l, c = row['open'], row['high'], row['low'], row['close']
                        bb         = min(o, c)
                        bt         = max(o, c)
                        body       = bt - bb
                        lower_wick = bb - l
                        upper_wick = h - bt
                        half_body  = body / 2

                        # Evaluate each rule individually
                        sup_r1 = lower_wick >= half_body          # wick >= half body
                        sup_r2 = l <= bep_val - 1.5               # wick below BEP-1.5
                        sup_r3 = o >= bep_val + 0.4               # open above BEP+0.4
                        sup_r4 = c >= bep_val + 1                 # close above BEP+1
                        sup_pass = sup_r1 and sup_r2 and sup_r3 and sup_r4

                        res_r1 = upper_wick >= half_body          # wick >= half body
                        res_r2 = h >= bep_val + 1.5               # wick above BEP+1.5
                        res_r3 = o <= bep_val - 0.4               # open below BEP-0.4
                        res_r4 = c <= bep_val - 1                 # close below BEP-1
                        res_pass = res_r1 and res_r2 and res_r3 and res_r4

                        # Determine which rules failed (for quick diagnosis)
                        def rule_str(rules, labels):
                            fails = [lbl for ok, lbl in zip(rules, labels) if not ok]
                            return "FAIL: " + ", ".join(fails) if fails else "ALL PASS"

                        sup_labels = [
                            f"lower_wick({lower_wick:.2f})>=half_body({half_body:.2f})",
                            f"low({l:.2f})<=BEP-1.5({bep_val-1.5:.2f})",
                            f"open({o:.2f})>=BEP+0.4({bep_val+0.4:.2f})",
                            f"close({c:.2f})>=BEP+1({bep_val+1:.2f})",
                        ]
                        res_labels = [
                            f"upper_wick({upper_wick:.2f})>=half_body({half_body:.2f})",
                            f"high({h:.2f})>=BEP+1.5({bep_val+1.5:.2f})",
                            f"open({o:.2f})<=BEP-0.4({bep_val-0.4:.2f})",
                            f"close({c:.2f})<=BEP-1({bep_val-1:.2f})",
                        ]

                        entry = {
                            'Time':      row['timestamp'].strftime('%H:%M'),
                            'Open':      round(o, 2),
                            'High':      round(h, 2),
                            'Low':       round(l, 2),
                            'Close':     round(c, 2),
                            'Body':      round(body, 2),
                            'LowerWick': round(lower_wick, 2),
                            'UpperWick': round(upper_wick, 2),
                            'HalfBody':  round(half_body, 2),
                            'Signal':    ('✅ SUPPORT' if sup_pass
                                          else '✅ RESISTANCE' if res_pass
                                          else '—'),
                        }
                        if show_rule_check:
                            entry['SUP Rules'] = (
                                '✅ ALL PASS' if sup_pass
                                else rule_str([sup_r1,sup_r2,sup_r3,sup_r4], sup_labels)
                            )
                            entry['RES Rules'] = (
                                '✅ ALL PASS' if res_pass
                                else rule_str([res_r1,res_r2,res_r3,res_r4], res_labels)
                            )
                        display_rows.append(entry)

                    df_display = pd.DataFrame(display_rows).sort_values(
                        'Time', ascending=False
                    )

                    # Colour rows: green = SUPPORT signal, red = RESISTANCE, grey = nothing
                    def colour_debug_row(row):
                        if '✅ SUPPORT'    in str(row.get('Signal', '')):
                            return ['background:rgba(38,166,154,0.25)'] * len(row)
                        if '✅ RESISTANCE' in str(row.get('Signal', '')):
                            return ['background:rgba(239,83,80,0.25)'] * len(row)
                        return [''] * len(row)

                    st.dataframe(
                        df_display.style.apply(colour_debug_row, axis=1),
                        width='stretch',
                        height=420
                    )

                    # Quick lookup: enter a specific candle time to see full rule detail
                    st.markdown("**🔍 Candle-level rule checker**")
                    st.caption("Enter a candle time (e.g. 13:15) to see the exact pass/fail for every rule")
                    chk_time = st.text_input(
                        "Candle time (HH:MM)", value="", placeholder="13:15",
                        key="dbg_candle_time"
                    )
                    if chk_time.strip():
                        match = df_raw[
                            df_raw['timestamp'].dt.strftime('%H:%M') == chk_time.strip()
                        ]
                        if match.empty:
                            st.warning(f"No candle found at {chk_time} for {selected_key}. "
                                       f"Available times: "
                                       f"{', '.join(df_raw['timestamp'].dt.strftime('%H:%M').tolist())}")
                        else:
                            row = match.iloc[0]
                            o, h, l, c = row['open'], row['high'], row['low'], row['close']
                            bb         = min(o, c)
                            bt         = max(o, c)
                            body       = bt - bb
                            lower_wick = bb - l
                            upper_wick = h - bt
                            half_body  = body / 2

                            st.markdown(f"#### {selected_key.replace('_',' ')} @ {chk_time} | BEP: {bep_val:.2f}")
                            c1, c2 = st.columns(2)
                            with c1:
                                st.markdown("**SUPPORT rules:**")
                                st.markdown(
                                    f"- R1 lower_wick({lower_wick:.2f}) >= half_body({half_body:.2f}): "
                                    f"{'✅' if lower_wick >= half_body else '❌'}\n"
                                    f"- R2 low({l:.2f}) <= BEP-1.5({bep_val-1.5:.2f}): "
                                    f"{'✅' if l <= bep_val-1.5 else '❌'}\n"
                                    f"- R3 open({o:.2f}) >= BEP+0.4({bep_val+0.4:.2f}): "
                                    f"{'✅' if o >= bep_val+0.4 else '❌'}\n"
                                    f"- R4 close({c:.2f}) >= BEP+1({bep_val+1:.2f}): "
                                    f"{'✅' if c >= bep_val+1 else '❌'}"
                                )
                            with c2:
                                st.markdown("**RESISTANCE rules:**")
                                st.markdown(
                                    f"- R1 upper_wick({upper_wick:.2f}) >= half_body({half_body:.2f}): "
                                    f"{'✅' if upper_wick >= half_body else '❌'}\n"
                                    f"- R2 high({h:.2f}) >= BEP+1.5({bep_val+1.5:.2f}): "
                                    f"{'✅' if h >= bep_val+1.5 else '❌'}\n"
                                    f"- R3 open({o:.2f}) <= BEP-0.4({bep_val-0.4:.2f}): "
                                    f"{'✅' if o <= bep_val-0.4 else '❌'}\n"
                                    f"- R4 close({c:.2f}) <= BEP-1({bep_val-1:.2f}): "
                                    f"{'✅' if c <= bep_val-1 else '❌'}"
                                )

                    st.download_button(
                        f"⬇️ Download raw candles ({selected_key})",
                        df_raw.to_csv(index=False),
                        f"raw_candles_{selected_key}.csv",
                        "text/csv",
                        key="dbg_download_raw"
                    )

    # ── PERSISTENT SIGNAL LOG VIEWER ───────────────────────────────────
    st.divider()
    st.subheader("📁 Signal History Log (Persistent)")
    st.caption(f"Logs saved to: `{LOG_DIR}`  — survives app restarts and browser close")

    log_files = list_log_files()

    if not log_files:
        st.info("No signal logs yet. Signals will be automatically saved here as they are detected.")
    else:
        tab_today, tab_history = st.tabs(["📅 Today's Log", "🗂 All History"])

        with tab_today:
            df_today = load_signal_log()
            if df_today.empty:
                st.info("No signals logged today yet.")
            else:
                # Summary metrics
                m1, m2, m3, m4 = st.columns(4)
                m1.metric("Total Signals Today", len(df_today))
                m2.metric("Support",   len(df_today[df_today['Signal']=='SUPPORT']))
                m3.metric("Resistance",len(df_today[df_today['Signal']=='RESISTANCE']))
                conf_times = df_today.groupby('Candle Time').size()
                m4.metric("Confluence Times", int((conf_times >= 2).sum()))

                # Highlight support/resistance in log too
                def hl_log(row):
                    if row['Signal'] == 'SUPPORT':
                        return ['background:rgba(38,166,154,0.2)'] * len(row)
                    return ['background:rgba(239,83,80,0.2)'] * len(row)

                st.dataframe(
                    df_today.sort_values('Candle Time', ascending=False)
                             .style.apply(hl_log, axis=1),
                    width='stretch', height=400
                )
                st.download_button(
                    "⬇️ Download Today's Log",
                    df_today.to_csv(index=False),
                    f"bep_log_{datetime.now().strftime('%Y%m%d')}.csv",
                    "text/csv",
                    key="dl_today_log"
                )

                # Confluence summary from log
                conf_df = df_today.groupby('Candle Time').filter(lambda x: len(x) >= 2)
                if not conf_df.empty:
                    st.markdown("**⚡ Confluence candles today:**")
                    for ct, grp in conf_df.groupby('Candle Time'):
                        strikes_info = '  |  '.join(
                            f"{r['Strike']} {r['Type']} ({r['Signal'][0]})"
                            for _, r in grp.iterrows()
                        )
                        st.markdown(
                            f"<div class='conf-box'><b>{ct}</b> — {strikes_info}</div>",
                            unsafe_allow_html=True
                        )

        with tab_history:
            selected_file = st.selectbox(
                "Select date", log_files,
                format_func=lambda f: f.replace('bep_signals_','').replace('.csv','')
            )
            if selected_file:
                hist_path = os.path.join(LOG_DIR, selected_file)
                try:
                    df_hist = pd.read_csv(hist_path)
                    st.caption(f"{len(df_hist)} signals on this date")
                    st.dataframe(
                        df_hist.sort_values('Candle Time', ascending=False),
                        width='stretch', height=400
                    )
                    st.download_button(
                        "⬇️ Download",
                        df_hist.to_csv(index=False),
                        selected_file,
                        "text/csv",
                        key="dl_hist_log"
                    )
                except Exception as e:
                    st.error(f"Could not read log: {e}")

    # ── CHARTS BY TIME ────────────────────────────────────────────────
    if grouped2:
        st.subheader("📉 Confluence Charts by Time")
        for time_key, sigs in grouped2.items():
            with st.expander(
                f"{time_key} — {len(sigs)} signal(s) "
                f"{'⚡ Confluence' if len(sigs) >= 2 else ''}"
            ):
                cols = st.columns(min(len(sigs), 2))
                for idx, sig in enumerate(sigs):
                    key = f"{sig.strike}_{sig.option_type}"
                    df_chart = (st.session_state.demo_candles.get(key) if demo_mode
                                else st.session_state.scanner.candle_history.get(key))
                    if df_chart is not None:
                        with cols[idx % 2]:
                            fig = render_chart(df_chart, sig.bep, [sig],
                                               f"{sig.strike} {sig.option_type} | {sig.signal_type}")
                            st.plotly_chart(fig, width='stretch',
                                            key=f"chart_{time_key}_{idx}")
                            css   = "sig-support" if sig.signal_type == 'SUPPORT' else "sig-resist"
                            entry = ("Close > BEP" if sig.signal_type == 'SUPPORT'
                                     else "Close < BEP")
                            stop  = (f"Below wick {sig.wick_low:.1f}"
                                     if sig.signal_type == 'SUPPORT'
                                     else f"Above wick {sig.wick_high:.1f}")
                            st.markdown(f"""
                            <div class="{css}">
                                <b>{sig.signal_type}</b> &nbsp;|&nbsp;
                                O:{sig.open:.1f} H:{sig.high:.1f}
                                L:{sig.low:.1f} C:{sig.close:.1f}<br>
                                <small>Entry: {entry} &nbsp;|&nbsp; Stop: {stop}</small>
                            </div>
                            """, unsafe_allow_html=True)
    if not all_signals:
        st.info("No confluence signals yet (need CE + PE rejection at same candle time)")
        st.subheader("📖 Strategy Rules")
        c1, c2 = st.columns(2)
        with c1:
            st.markdown("""
            **SUPPORT Rejection (Buy)**
            - Wick dips **below** BEP
            - Body closes **above** BEP
            - Entry: Close price
            - Stop: Below wick low
            - Applies to both **CE and PE**
            """)
        with c2:
            st.markdown("""
            **RESISTANCE Rejection (Sell)**
            - Wick pokes **above** BEP
            - Body closes **below** BEP
            - Entry: Close price
            - Stop: Above wick high
            - Applies to both **CE and PE**
            """)
        st.markdown(
            "**Confluence** — CE & PE both reject BEP at the same 5-min candle = "
            "high-probability setup 🔥"
        )

    # ── Market status bar ─────────────────────────────────────────────
    mkt_status, mkt_color, secs_left = get_market_status()
    is_live = mkt_status.startswith("LIVE")

    status_col1, status_col2, status_col3 = st.columns([2, 2, 3])
    with status_col1:
        st.markdown(
            f"<span style='color:{mkt_color};font-weight:bold;font-size:1.1rem'>"
            f"Market: {mkt_status}</span>",
            unsafe_allow_html=True
        )
    with status_col2:
        if is_live and secs_left > 0:
            st.markdown(
                f"<span style='color:#888'>Next candle closes in: "
                f"<b style='color:#00d4ff'>{secs_left}s</b></span>",
                unsafe_allow_html=True
            )
    with status_col3:
        if is_live:
            st.caption("📌 Tip: Enable Live Auto-Scan in sidebar for real-time confluence alerts")
        else:
            st.caption("📌 After-market: Use 'Scan Signals' for full historical analysis")

    # ── Auto live scan logic ───────────────────────────────────────────
    if auto_refresh and not demo_mode and "scanner" in st.session_state:
        if is_live:
            # Smart wait: sleep until just after the next candle closes
            wait = max(secs_left + 3, 10)  # +3 sec buffer for API to update
            st.info(
                f"⏱ Live scan active — next scan in **{wait}s** "
                f"(after {(datetime.now() + timedelta(seconds=wait)).strftime('%H:%M:%S')} candle closes)"
            )
            time.sleep(wait)
            # Incremental scan — only latest candle
            scanner = st.session_state.scanner
            with st.spinner("Live scan: checking latest candle…"):
                new_sigs, scan_errs = scanner.scan_latest_candle()
            st.session_state.signals = scanner.signals
            st.session_state.last_scan = datetime.now()
            if new_sigs:
                notify("NEW BEP SIGNAL",
                       f"{len(new_sigs)} new signal(s) detected!",
                       level="success", tag=f"live_{datetime.now().strftime('%H%M')}")
            st.rerun()
        else:
            st.info("⏸ Live scan paused — market is closed")


if __name__ == "__main__":
    main()
