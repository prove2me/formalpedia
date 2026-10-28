-- Prove2me | Theorems.Thm_BitcoinMerkle_hasEqualPair_append_even
-- name    : BitcoinMerkle.hasEqualPair_append_even
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:26:17.955994+00:00
-- url     : https://prove2.me/theorems/3180f273-606e-4a5f-92af-faaa2165c74c
-- title:
--   The mutation test distributes over an even split
-- statement:
--   For all lists $\ell, r$ with $|\ell|$ even, $\mathrm{hasEqualPair}(\ell \mathbin{+\!\!+} r) = \mathrm{hasEqualPair}(\ell) \lor \mathrm{hasEqualPair}(r)$. With aligned pair boundaries, an equal aligned pair of the concatenation lies entirely in $\ell$ or entirely in $r$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.hasEqualPair_append_even {H : Type} [DecidableEq H] :
    ∀ (l r : List H), l.length % 2 = 0 →
      BitcoinMerkle.hasEqualPair (l ++ r) = (BitcoinMerkle.hasEqualPair l || BitcoinMerkle.hasEqualPair r) := by sorry
