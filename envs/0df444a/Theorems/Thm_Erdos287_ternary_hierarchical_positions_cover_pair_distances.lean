-- Prove2me | Theorems.Thm_Erdos287_ternary_hierarchical_positions_cover_pair_distances
-- name    : Erdos287.ternary_hierarchical_positions_cover_pair_distances
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:04:35.434043+00:00
-- url     : https://prove2.me/theorems/00646e0b-e614-53cf-8aed-fa983ad9b9c3
-- title:
--   Ternary hierarchical positions place 81 points using four prescribed distance scales
-- statement:
--   Let $w_0,\ldots,w_{k-1}$ be positive integers with $w_{i+1}\ge64w_i$. There is a set of $3^k$ natural positions at most $2\sum_i w_i$ such that each positive pair difference $d$ satisfies $(61/63)w_i\le d\le(128/63)w_i$ for some $i$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Ternary geometry for excluding multiplicatively separated maximal denominators.

import Mathlib

theorem Erdos287.ternary_hierarchical_positions_cover_pair_distances (w : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j < k, 0 < w j)
    (hsep : ∀ j, j + 1 < k → 64 * w j ≤ w (j + 1)) :
    ∃ S : Finset ℕ, S.card = 3 ^ k ∧
      (∀ x ∈ S, x ≤ 2 * ∑ j ∈ Finset.range k, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < k,
        61 * w j ≤ 63 * (y - x) ∧ 63 * (y - x) ≤ 128 * w j := by sorry
