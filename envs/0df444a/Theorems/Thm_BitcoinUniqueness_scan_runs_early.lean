-- Prove2me | Theorems.Thm_BitcoinUniqueness_scan_runs_early
-- name    : BitcoinUniqueness.scan_runs_early
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:47:50.055621+00:00
-- url     : https://prove2.me/theorems/41c2c12c-4407-4465-8eb7-bd0b2f97e3da
-- title:
--   Before the BIP34 block can be an ancestor, the scan runs except at the two repeats
-- statement:
--   If the state has at most 227,931 headers and the block is not one of the two `IsBIP30Repeat` blocks at its height, then `ScanRuns S b`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_runs_early (S : ChainState) (b : BitcoinSer.Block)
    (h : S.headers.length ≤ BitcoinHeader.BIP34Height)
    (hrep : BitcoinBlockV2.isBIP30Repeat S.nextHeight (BitcoinSer.headerHash b.header) = false) :
    BitcoinUniqueness.ScanRuns S b := by sorry
