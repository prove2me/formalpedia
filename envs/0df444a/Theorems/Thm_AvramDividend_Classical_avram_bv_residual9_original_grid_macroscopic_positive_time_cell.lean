-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_grid_macroscopic_positive_time_cell
-- name    : AvramDividend.Classical.avram_bv_residual9_original_grid_macroscopic_positive_time_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:43:51.769601+00:00
-- url     : https://prove2.me/theorems/1adc3963-5808-46b6-a1f7-ffaf67362c92
-- title:
--   Original arbitrary grids admit a macroscopic generator cell beginning at positive time
-- statement:
--   Construct an exact original hgrid/hmono family with u(n,1)>0 and the next physical time cell at least T/4 for every n>=1. This is a stronger relevant obstruction to generic vanishing Taylor/Euler residuals than a large first cell at time zero; the witness is extracted from the Proved nonuniform grid construction and retains all endpoints.
-- source:
--   BV-RESIDUAL9 physical stopped-grid consistency analysis

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_grid_macroscopic_positive_time_cell
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, 1 ≤ n →
        0 < (u n 1 : ℝ) ∧
        T / 4 ≤ (u n 2 : ℝ) - (u n 1 : ℝ)) := by sorry
