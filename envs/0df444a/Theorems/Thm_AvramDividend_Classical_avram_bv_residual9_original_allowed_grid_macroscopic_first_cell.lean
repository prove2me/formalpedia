-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_allowed_grid_macroscopic_first_cell
-- name    : AvramDividend.Classical.avram_bv_residual9_original_allowed_grid_macroscopic_first_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:56:48.737279+00:00
-- url     : https://prove2.me/theorems/12282aaa-0e67-48cf-959d-7e2419bc68ef
-- title:
--   Original monotone endpoint grid permits a first cell at least half the full horizon
-- statement:
--   Under the exact universal grid geometry in the canonical BV residual theorem, construct one valid grid with first time cell width at least T/2 for every n. This quantitatively establishes that hgrid and hmono alone cannot imply shrinking mesh, because a fixed positive width survives as n grows. It imports only the independently Proved original-grid nonuniform counterexample, not any stochastic martingale or derivative theorem.
-- source:
--   BV-RESIDUAL9 quantitative missing-refinement certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_monotone_grid_nonuniform_counterexample
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_allowed_grid_macroscopic_first_cell
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n, T / 2 ≤ (u n 1 : ℝ) - (u n 0 : ℝ)) := by sorry
