-- Prove2me | Theorems.Thm_BitcoinUniqueness_coinbases_distinct
-- name    : BitcoinUniqueness.coinbases_distinct
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T13:48:14.423693+00:00
-- url     : https://prove2.me/theorems/830c71a4-5af0-46f2-b9a3-8c71babb2342
-- title:
--   Blocks accepted at different post-BIP34 heights have different coinbase scriptSigs
-- statement:
--   For two reachable states at next heights $h_1 \ne h_2$, both $\ge 227{,}931$ and $< 2^{31}$, and blocks accepted on them: the coinbase `scriptSig`s differ. Each starts with its own height push, and if both pushes were prefixes of the same bytes the shorter would prefix the longer, forcing equal heights.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem BitcoinUniqueness.coinbases_distinct (S₁ S₂ : ChainState) (b₁ b₂ : BitcoinSer.Block) (now₁ now₂ : Int)
    (S₁' S₂' : ChainState) (undo₁ undo₂ : BlockUndo)
    (hR₁ : BitcoinBlockV2.Reachable S₁) (hR₂ : BitcoinBlockV2.Reachable S₂)
    (h₁ : BitcoinBlockV2.validate S₁ b₁ now₁ = .accept S₁' undo₁) (h₂ : BitcoinBlockV2.validate S₂ b₂ now₂ = .accept S₂' undo₂)
    (h34₁ : BitcoinHeader.BIP34Height ≤ S₁.nextHeight) (h34₂ : BitcoinHeader.BIP34Height ≤ S₂.nextHeight)
    (hlt₁ : S₁.nextHeight < 2 ^ 31) (hlt₂ : S₂.nextHeight < 2 ^ 31) (hne : S₁.nextHeight ≠ S₂.nextHeight) :
    BitcoinUniqueness.coinbaseScriptSig b₁ ≠ BitcoinUniqueness.coinbaseScriptSig b₂ := by sorry
