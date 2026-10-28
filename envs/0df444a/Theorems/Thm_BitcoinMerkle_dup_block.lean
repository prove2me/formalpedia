-- Prove2me | Theorems.Thm_BitcoinMerkle_dup_block
-- name    : BitcoinMerkle.dup_block
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T04:26:37.346026+00:00
-- url     : https://prove2.me/theorems/4b701848-9672-453b-a499-434716868843
-- title:
--   CVE-2012-2459 in general: duplicating an aligned trailing block
-- statement:
--   For every pairwise hash $c$, zero hash $z$, level $k \in \mathbb N$, non-empty list $\ell$ whose length is a multiple of $2^{k+1}$, and block $t$ of exactly $2^{k}$ hashes,
--   $$\mathrm{root}(\ell \mathbin{+\!\!+} t) = \mathrm{root}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t) \qquad\text{and}\qquad \mathrm{mutated}(\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t) = \mathtt{true},$$
--   where root and mutated are the two components of $\mathrm{computeMerkleRoot}_{c,z}$, the transcription of `ComputeMerkleRoot`.
--
--   Under the alignment hypotheses, $t$ occupies a complete aligned subtree that collapses to a single node after $k$ levels; at that level $\ell \mathbin{+\!\!+} t$ has odd length and the source duplicates the node, while $\ell \mathbin{+\!\!+} t \mathbin{+\!\!+} t$ already carries the copy as an equal aligned pair. The two computations then coincide, and the copy is detected by the per-level check. With $k = 0$ this is the duplicated last transaction; with $k = 1$ and $\ell$ of length four it is the $[1,2,3,4,5,6]$ versus $[1,2,3,4,5,6,5,6]$ example of the source comment.
--
--   This is the general statement of the defence against CVE-2012-2459: every duplication of this shape is root-preserving, which is the attack, and is flagged, which is the defence. Nothing is assumed about $c$; the result is about the loop structure alone.
--
--   **Formalization Note.** The non-emptiness of $\ell$ is necessary, since a single-node list is returned without processing while its doubled form is hashed once more. The statement is proved for the loop with an arbitrary incoming flag and specialized to `computeMerkleRoot`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, ComputeMerkleRoot, src/consensus/merkle.cpp lines 51-73, with the CVE-2012-2459 comment at lines 16-50: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/merkle.cpp#L51

import Definitions.Def_BitcoinMerkle

theorem BitcoinMerkle.dup_block {H : Type} [DecidableEq H] (c : H → H → H) (z : H) :
    ∀ (k : Nat) (l t : List H), l ≠ [] → l.length % 2 ^ (k + 1) = 0 → t.length = 2 ^ k →
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t)).1 = (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).1 ∧
      (BitcoinMerkle.computeMerkleRoot c z (l ++ t ++ t)).2 = true := by sorry
