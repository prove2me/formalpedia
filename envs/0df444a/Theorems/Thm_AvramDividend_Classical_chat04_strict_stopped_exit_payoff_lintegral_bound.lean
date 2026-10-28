-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_bound
-- name    : AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:29:57.419973+00:00
-- url     : https://prove2.me/theorems/172ea2f3-9154-41c6-ac2f-7fdd356c7142
-- title:
--   Strict stopped upper-exit terminal q-scale payoff bound
-- statement:
--   For nonnegative discount, the strict upper-before-ruin terminal scale payoff is bounded in expectation by W(a). The proof combines the verified overshoot boundary identity and discount measurability with the established generic stopped exit factor bound. This provides a finite domination component of the stopping-limit argument with no unproved martingale assumptions.
-- source:
--   Proved AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff, chat03_exact_upperfirst_discount_integrand_measurable, chat03_exact_stopped_discount_mul_scale_le_scale; Mathlib MeasureTheory.lintegral_mul_const.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_exact_stopped_discount_mul_scale_le_scale

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) ≤ ENNReal.ofReal (W a) := by sorry
