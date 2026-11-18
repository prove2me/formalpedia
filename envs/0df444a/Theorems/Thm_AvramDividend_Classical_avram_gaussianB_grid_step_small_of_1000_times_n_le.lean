-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_grid_step_small_of_1000_times_n_le
-- name    : AvramDividend.Classical.avram_gaussianB_grid_step_small_of_1000_times_n_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:42:58.181417+00:00
-- url     : https://prove2.me/theorems/e05840bd-ee6f-45ac-bf9c-24298c15c39a
-- title:
--   Original physical-grid step is within the 1/1000 Brownian tube extension whenever m+1≥1000n
-- statement:
--   For physical mesh step Δ=n/(m+1), the explicit natural-number refinement condition m+1≥1000n forces Δ≤1/1000. This is the uniform refining-grid bound needed to apply a fixed centred Brownian small-ball event through one additional mesh cell in the original stopped Gaussian martingale source.

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_grid_step_small_of_1000_times_n_le
    (n m : ℕ) (hm : 1000 * n ≤ m + 1) :
    (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) ≤ (1 / 1000 : ℝ≥0) := by sorry
