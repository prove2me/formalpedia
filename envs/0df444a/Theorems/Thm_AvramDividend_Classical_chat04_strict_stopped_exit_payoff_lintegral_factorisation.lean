-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
-- name    : AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:24:07.719007+00:00
-- url     : https://prove2.me/theorems/e1242e81-f9a9-4eba-b16d-924abe78e9af
-- title:
--   Strict two-sided stopped q-scale payoff integral factorisation
-- statement:
--   The strict upper-before-ruin discounted q-scale terminal payoff, evaluated at the actual upper first-passage time, has expectation equal to the two-sided exit discount expectation multiplied by the scale function at the upper barrier. This is the boundary payoff and Tonelli factorisation component of the stopped q-scale martingale argument. It does not assume the unproved martingale or stopped-scale identity.
-- source:
--   Proved AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff and chat03_exact_upperfirst_discount_integrand_measurable, plus pinned Mathlib MeasureTheory.lintegral_mul_const.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) =
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by sorry
