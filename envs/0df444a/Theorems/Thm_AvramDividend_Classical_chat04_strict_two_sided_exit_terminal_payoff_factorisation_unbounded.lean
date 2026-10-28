-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
-- name    : AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:13:33.063972+00:00
-- url     : https://prove2.me/theorems/5b55cf54-0f29-4976-99b7-8dc6dfac1a44
-- title:
--   Unbounded-variation two-sided exit terminal q-scale payoff factorisation
-- statement:
--   For any spectrally negative Lévy process of unbounded variation, q>0, q-scale function W and x≤a, the expectation of the combined strict upper-exit and lower-ruin stopped scale payoff equals the discounted strict upper-exit expectation times W(a). Unlike the boundary theorem, no W(0)=0 hypothesis is required: it follows from the unbounded-variation dichotomy and the Gaussian or infinite-small-jump zero-origin theorems. This establishes the exact terminal boundary contribution needed before killed optional stopping.
-- source:
--   Proved chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero; unbounded_variation_gaussian_or_infinite_small_jump_moment; scaleFunction_zero_origin_gaussian_without_standing; scaleFunction_zero_origin_infinite_small_jumps.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_of_Wzero
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
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
