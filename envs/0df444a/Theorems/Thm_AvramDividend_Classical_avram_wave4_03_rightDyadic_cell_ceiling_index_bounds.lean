-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
-- name    : AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:47:22.60552+00:00
-- url     : https://prove2.me/theorems/6752dded-571a-40a7-a891-90d628e65f31
-- title:
--   Exact upper-ceiling dyadic Stieltjes cell index bounds
-- statement:
--   For a strictly positive normalised time not exceeding one, the upward ceiling of its positive integer mesh multiple is a valid positive grid-cell index bounded by the number of cells. The time lies strictly after the preceding cell coordinate and at or before the upper coordinate. This index lemma is a precise prerequisite to identify the source Lévy double-Fatou right-ceiling Stieltjes integrand with the actual finite-grid step stochastic cash budget.
-- source:
--   Pinned Nat.le_ceil, Nat.ceil_lt_add_one, Nat.ceil_le, elementary positive real arithmetic.

import Mathlib
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let k := Nat.ceil (y * (N : ℝ))
    0 < k ∧ k ≤ N ∧ ((k : ℝ) - 1) < y * (N : ℝ) ∧
      y * (N : ℝ) ≤ (k : ℝ) := by sorry
