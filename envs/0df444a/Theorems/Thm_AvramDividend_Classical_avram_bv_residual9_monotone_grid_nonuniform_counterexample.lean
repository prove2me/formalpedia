-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
-- name    : AvramDividend.Classical.avram_bv_residual9_monotone_grid_nonuniform_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:42:03.881854+00:00
-- url     : https://prove2.me/theorems/66002633-4ea8-4db4-ba4d-211e6011a0c9
-- title:
--   Original stopped physical-grid endpoint and monotonicity conditions permit a non-refining partition
-- statement:
--   For every positive horizon T construct a monotone grid satisfying literally the arbitrary-grid hypotheses of avram_a19_original_physical_stopped_residual_for_grid, with all positive-index clock points equal to its last clock. The grid violates the uniform clock-coordinate identity. This is an exact counterexample to inferring shrinking or uniform physical cells from hgrid and hmono alone, not a disproof of the full stochastic theorem.
-- source:
--   BV-RESIDUAL9 source-exact monotone-grid geometry counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_monotone_grid_nonuniform_counterexample
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, u n 1 = u n (n + 1)) ∧
      ¬ (∀ n i, (u n i : ℝ) =
        T * (i : ℝ) / ((n : ℝ) + 2)) := by sorry
