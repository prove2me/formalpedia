-- Prove2me | Theorems.Thm_BitcoinUniqueness_coinbase_height_prefix
-- name    : BitcoinUniqueness.coinbase_height_prefix
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:48:02.396137+00:00
-- url     : https://prove2.me/theorems/c61ace72-9e2a-4d08-abae-f778f3af5175
-- title:
--   An accepted post-BIP34 block's coinbase starts with its height push
-- statement:
--   For a reachable state at next height $\ge 227{,}931$ and an accepted block: `heightScript S.nextHeight` is a prefix of `coinbaseScriptSig b`. From the acceptance theorem's contextual clause (`ContextualCheckBlock`'s `bad-cb-height`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.coinbase_height_prefix (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) :
    (BitcoinBlockV2.heightScript S.nextHeight).isPrefixOf (BitcoinUniqueness.coinbaseScriptSig b) = true := by sorry
