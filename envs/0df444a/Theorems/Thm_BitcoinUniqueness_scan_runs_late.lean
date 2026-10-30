-- Prove2me | Theorems.Thm_BitcoinUniqueness_scan_runs_late
-- name    : BitcoinUniqueness.scan_runs_late
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:47:39.417991+00:00
-- url     : https://prove2.me/theorems/1f76a5a4-39ec-42f8-9832-d1fe85edfaa4
-- title:
--   From height 1,983,702 the scan always runs
-- statement:
--   If `BIP34_IMPLIES_BIP30_LIMIT ≤ S.nextHeight` then `ScanRuns S b` for every block `b`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_runs_late (S : ChainState) (b : BitcoinSer.Block)
    (h : BIP34_IMPLIES_BIP30_LIMIT ≤ S.nextHeight) : BitcoinUniqueness.ScanRuns S b := by sorry
