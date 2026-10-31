-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_3
-- name    : BulteauTranspositions.NPHard.property_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:52:09.710165+00:00
-- url     : https://prove2.me/theorems/8320aa33-d452-41a3-9197-0bc959015fd0
-- title:
--   Property 3 — adjacency preservation and at most three removed breakpoints
-- statement:
--   Let π be any sentinel permutation on {0,…,n} and let τ=τ(i,j,k) with 0<i<j<k≤n. For every x∈{1,…,n} outside {i,j,k}, adjacency at x in π holds if and only if adjacency at τ⁻¹(x) holds in π∘τ. Moreover, d_b(π∘τ)≥d_b(π)−3. Both adjacency equivalence and the total breakpoint bound are asserted.
--
--   Differences from the source:
--   - encoding: bijections on {0,…,n} with the two fixed sentinels → natural-valued functions restricted by IsPermutation on that interval; reason: values outside the finite interval are unused; every source permutation has such an extension
--   - encoding: d_b(π∘τ)≥d_b(π)−3 → d_b(π)≤d_b(π∘τ)+3; reason: addition expresses the exact integer inequality without truncated subtraction
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 3, printed p. 3 = PDF p. 3; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Sorting

namespace BulteauTranspositions.NPHard

theorem property_3 (n : ℕ) (p : ℕ → ℕ) (hp : IsPermutation n p) (c : Cut) (hc : c.Legal n) :
    (∀ x ∈ Finset.Icc 1 n, x ≠ c.i → x ≠ c.j → x ≠ c.k →
      (adjacency p x ↔ adjacency (applyMove p c) (c.inv.tau x))) ∧
    breakpoints n p ≤ breakpoints n (applyMove p c) + 3 := by sorry

end BulteauTranspositions.NPHard
