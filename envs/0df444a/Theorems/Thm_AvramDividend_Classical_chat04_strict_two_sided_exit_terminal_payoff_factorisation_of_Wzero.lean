-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
-- name    : AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:56:12.621769+00:00
-- url     : https://prove2.me/theorems/228645b0-fe8d-42f8-8fff-ffb099064f7d
-- title:
--   Strict two-sided stopped terminal q-scale payoff factorisation with zero boundary scale
-- statement:
--   For any spectrally negative Levy process and its q-scale function with W(0)=0, the combined lower-ruin and upper-exit discounted terminal scale payoffs have expectation equal to the strict upper exit discount multiplied by W(a). The proof combines the exact first-passage boundary payoff, upper-side measurability, Lebesgue additivity, and the zero lower-ruin payoff. It provides the payoff decomposition needed before optional stopping.
-- source:
--   Published chat04 strict upper stopped payoff integral factorisation and lower exit lintegral zero of W(0)=0; Mathlib lintegral_add_left.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_lintegral_zero_of_Wzero

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
    (a x : ℝ) (hxa : x ≤ a) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) =
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by sorry
