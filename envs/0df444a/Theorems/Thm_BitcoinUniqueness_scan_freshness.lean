-- Prove2me | Theorems.Thm_BitcoinUniqueness_scan_freshness
-- name    : BitcoinUniqueness.scan_freshness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:47:26.174089+00:00
-- url     : https://prove2.me/theorems/69f95bfd-ad9d-4b33-94a2-7f4e592e112e
-- title:
--   Where the BIP30 scan runs, an accepted block's outputs are fresh
-- statement:
--   For a reachable state, an accepted block (not hashing to the genesis hash) and `ScanRuns S b`: `FreshOutputs S.utxo b`. From the acceptance theorem: the ledger predicate's BIP30 clause.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.scan_freshness (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (hscan : BitcoinUniqueness.ScanRuns S b) (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash) :
    BitcoinUniqueness.FreshOutputs S.utxo b := by sorry
