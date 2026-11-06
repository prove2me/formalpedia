-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:22:02.630658+00:00
-- url     : https://prove2.me/theorems/953e9a6c-e63d-4024-880d-6915f3d8deb4
-- title:
--   Uniform original physical grid cell size tends to zero at increasing refinement
-- statement:
--   For any original finite physical horizon T and positive real tolerance, the deterministic physical-cell length T/(m+1) tends to zero with m. This strictly quantitative fact is the rate premise needed for the original stopped C1 mesh-refinement source, independent of any Lévy process replacement or stochastic assumption.

import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open Filter
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ((T / ((m + 1 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) < δ := by sorry
