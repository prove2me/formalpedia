-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_grid_exact_cell_width
-- name    : AvramDividend.Classical.avram_a19_uniform_grid_exact_cell_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:06:15.657406+00:00
-- url     : https://prove2.me/theorems/e225bda7-c21f-44e3-b5a0-c735a2c19d00
-- title:
--   Exact physical uniform-grid cell width
-- statement:
--   On the explicit real-valued physical uniform grid, each adjacent cell has exactly width T/(n+2), allowing a uniform local error bound and explicit mesh control.
-- source:
--   Independent source-exact deterministic mesh identity underpinning the original-process stopped error estimate 965af42c. Contains no stochastic assumptions and is directly provable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_uniform_grid_exact_cell_width
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n i : ℕ) :
    (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2) := by sorry
