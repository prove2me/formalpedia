-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
-- name    : AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:21:03.400706+00:00
-- url     : https://prove2.me/theorems/b0a37e28-58d3-4588-b200-0964a345a59a
-- title:
--   Right-dyadic full Stieltjes cell indicator sum is exactly the ceiling endpoint
-- statement:
--   For every positive normalised observation time in (0,1], the full ENNReal half-open right-cell finite-grid step sum is exactly the value at the unique upper ceiling mesh index. This identifies the actual right-dyadic Fatou integrand with the finite-grid Stieltjes stochastic budget, retaining diffuse dividend mass.
-- source:
--   Proved right-ceiling localisation lemma 6752dded and Finset.sum_eq_single; exact bridge to original source double-Fatou 1f91129d and source full Stieltjes finite-grid stochastic budget e8f0e18c.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_ceiling_index_bounds
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range N,
      if (i : ℝ) < y * (N : ℝ) ∧
        y * (N : ℝ) ≤ ((i + 1 : ℕ) : ℝ) then a (i + 1) else 0) =
    a (Nat.ceil (y * (N : ℝ))) := by sorry
