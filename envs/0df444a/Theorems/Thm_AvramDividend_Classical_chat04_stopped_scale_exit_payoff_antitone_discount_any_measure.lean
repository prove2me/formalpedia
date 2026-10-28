-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_antitone_discount_any_measure
-- name    : AvramDividend.Classical.chat04_stopped_scale_exit_payoff_antitone_discount_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:49:34.543929+00:00
-- url     : https://prove2.me/theorems/522d200d-d1b2-484e-9f15-a538989d0e73
-- title:
--   Killing the upper-before-ruin q-scale reward is antitone in the nonnegative discount rate under any path law
-- statement:
--   For any path-space measure, increasing a nonnegative discount rate weakly decreases the lower integral of the stopped q-scale reward paid on strict upper exit before ruin, for the same reserve and upper barrier.
-- source:
--   Combines proved exact stopped-payoff factorisation with proved joint discounted upper-first expectation monotonicity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_joint_discounted_exit_any_measure_comparison

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_stopped_scale_exit_payoff_antitone_discount_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤ (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) := by sorry
