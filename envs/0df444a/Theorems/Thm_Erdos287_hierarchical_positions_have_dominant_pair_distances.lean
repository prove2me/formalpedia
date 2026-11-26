-- Prove2me | Theorems.Thm_Erdos287_hierarchical_positions_have_dominant_pair_distances
-- name    : Erdos287.hierarchical_positions_have_dominant_pair_distances
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T08:00:19.655485+00:00
-- url     : https://prove2.me/theorems/d55e898d-bdce-59e2-abf5-582e0352a5b9
-- title:
--   Hierarchical slope positions place all pair differences near six selected scales
-- statement:
--   Let $w_0,\ldots,w_{k-1}$ be positive integers with $w_{i+1}\ge64w_i$. There is a set of $2^k$ bounded natural positions with the following property. For any two distinct positions with difference $d>0$, there is a scale $w_i$ such that $(62/63)w_i\le d\le(64/63)w_i$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Hierarchical geometry for the multiplicatively separated maxima argument.

import Mathlib

theorem Erdos287.hierarchical_positions_have_dominant_pair_distances (w : ℕ → ℕ) (k : ℕ)
    (hpos : ∀ j < k, 0 < w j)
    (hsep : ∀ j, j + 1 < k → 64 * w j ≤ w (j + 1)) :
    ∃ S : Finset ℕ, S.card = 2 ^ k ∧
      (∀ x ∈ S, x ≤ ∑ j ∈ Finset.range k, w j) ∧
      ∀ x ∈ S, ∀ y ∈ S, x < y → ∃ j < k,
        62 * w j ≤ 63 * (y - x) ∧ 63 * (y - x) ≤ 64 * w j := by sorry
