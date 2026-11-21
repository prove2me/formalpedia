-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_nonnegative_sqrt_grid_rate_implies_mean_zero
-- name    : AvramDividend.Classical.avram_agentB_nonnegative_sqrt_grid_rate_implies_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:28:21.51817+00:00
-- url     : https://prove2.me/theorems/1f850e30-2e10-42fc-b820-9a21dabeeffa
-- title:
--   Any nonnegative expected original Gaussian mesh residual with uniform square-root-cell rate converges to zero
-- statement:
--   For the original finite-horizon uniform physical Gaussian mesh n/(m+1), every nonnegative real sequence a_m uniformly bounded by K sqrt(n/(m+1)) converges to zero. This is the exact analytical closing step from a quantitative source-exact Gaussian right-dividend atom energy bound to the parent expected absolute L1 convergence. Uses the explicit known reciprocal natural mesh limit, continuity of Real.sqrt at zero, scalar multiplication and squeeze.
-- source:
--   Mathlib tendsto_one_div_add_atTop_nhds_zero_nat, Real.continuous_sqrt, squeeze_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_nonnegative_sqrt_grid_rate_implies_mean_zero
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m)
    (hRate : ∀ m : ℕ, a m ≤
      K * Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ))) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by sorry
