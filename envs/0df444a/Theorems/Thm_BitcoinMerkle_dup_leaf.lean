-- Prove2me | Theorems.Thm_BitcoinMerkle_dup_leaf
-- name    : BitcoinMerkle.dup_leaf
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:26:27.233512+00:00
-- url     : https://prove2.me/theorems/100a8150-d913-4f42-bbaa-08038c1781e2
-- title:
--   CVE-2012-2459 at the leaf level: duplicate last transaction
-- statement:
--   For every $c$, $z$, non-empty list $\ell$ of even length and hash $a$,
--   $$\mathrm{root}(\ell \mathbin{+\!\!+} [a]) = \mathrm{root}(\ell \mathbin{+\!\!+} [a, a]) \qquad\text{and}\qquad \mathrm{mutated}(\ell \mathbin{+\!\!+} [a, a]) = \mathtt{true}.$$
--   The list $\ell \mathbin{+\!\!+} [a]$ has odd length, so the loop duplicates its last element; appending a second copy of $a$ explicitly produces the same first level, hence the same root, while the explicit copy forms an equal aligned pair and is flagged. Non-emptiness of $\ell$ is required: $[a]$ is its own root but $[a, a]$ hashes to $c(a,a)$.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.dup_leaf {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (l : List H) (a : H) (hne : l ≠ []) (heven : l.length % 2 = 0) :
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a])).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).1 ∧
    (BitcoinMerkle.computeMerkleRoot c z (l ++ [a, a])).2 = true := by sorry
