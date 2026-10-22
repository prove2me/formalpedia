-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_exact_uniform_grid_upperfirst_payoff_tendsto
-- name    : AvramDividend.Classical.chat03_exact_uniform_grid_upperfirst_payoff_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:58:25.936511+00:00
-- url     : https://prove2.me/theorems/ea079721-df73-4b99-a196-86bd4e51b295
-- title:
--   Exact uniform-grid discounted upper-first reward converges to official continuous reward
-- statement:
--   For separated upper and lower strict barriers, exact ENNReal uniform-grid first passage clocks converge pathwise to their official continuous named counterparts. Their upper-first discounted ENNReal reward therefore converges to the official strict upper-first reward, including trajectories with infinite passage clocks. The result combines both official sampled-clock convergence theorems, the accepted official no-finite-ties discounted payoff bridge, and upper no-exit persistence, without stochastic martingale hypotheses.
-- source:
--   Accepted official grid-discount-from-clock convergence theorem and new official upper/lower grid clock theorems at pinned Mathlib.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_grid_discount_tendsto_from_clock_convergence
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_exact_uniform_grid_upperfirst_payoff_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n =>
        let up := ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        let down := ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ∞
        if up < down then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
        else 0)
      atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by sorry
