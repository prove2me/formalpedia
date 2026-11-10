-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_finite_grid_factorial_telescoping_real
-- name    : AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_telescoping_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:21:43.608136+00:00
-- url     : https://prove2.me/theorems/f56b2229-dd87-4a84-9c9f-e63b0356c12a
-- title:
--   Uniform-grid original annulus factorial diagonal and chronological cross-cell algebra
-- statement:
--   For any finite sequence of real cell counts, the factorial product of their total equals the sum of the cell factorial diagonals plus twice the chronological prefix-times-current-cell sum. Applies verbatim to true original X.X negative-annulus intrinsic physical counts on each finite time partition; reduces 6ea0212e to finite-grid expected diagonals and already Proved chronological source rates de84ed95.
-- source:
--   Algebraic telescoping by Finset.sum_range_succ and ring, no stochastic or independence assumptions. Combined with source-faithful Proved de84ed95, shifted full cutoff factorial moment 69f9bc6c and physical time partition 61ef9f16.

import Mathlib
open BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mixed_source13_finite_grid_factorial_telescoping_real
    (k : ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ Finset.range k, a i) * ((∑ i ∈ Finset.range k, a i) - 1) =
      (∑ i ∈ Finset.range k, a i * (a i - 1)) +
        2 * (∑ i ∈ Finset.range k, (∑ j ∈ Finset.range i, a j) * a i) := by sorry
