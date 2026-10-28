-- Prove2me | Theorems.Thm_BitcoinMerkle_pairUp_append_even
-- name    : BitcoinMerkle.pairUp_append_even
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:26:09.132987+00:00
-- url     : https://prove2.me/theorems/02bc9fe3-f8dd-4fd3-9f92-0012e17a9248
-- title:
--   One level distributes over an even split
-- statement:
--   For every $c$ and lists $\ell, r$ with $|\ell|$ even, $\mathrm{pairUp}_c(\ell \mathbin{+\!\!+} r) = \mathrm{pairUp}_c(\ell) \mathbin{+\!\!+} \mathrm{pairUp}_c(r)$. When the prefix has even length the pair boundaries of the concatenation align with those of the two parts, so a level can be computed blockwise. The hypothesis is necessary: an odd prefix would pair its last element with the first element of $r$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.pairUp_append_even {H : Type} [DecidableEq H] (c : H → H → H) :
    ∀ (l r : List H), l.length % 2 = 0 → BitcoinMerkle.pairUp c (l ++ r) = BitcoinMerkle.pairUp c l ++ BitcoinMerkle.pairUp c r := by sorry
