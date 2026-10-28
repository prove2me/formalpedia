-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_negative_reserve
-- name    : AvramDividend.Classical.chat04_unbounded_stopped_scale_negative_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:31:09.154188+00:00
-- url     : https://prove2.me/theorems/821b7bc5-c333-4d86-a73a-0b769bb39d5b
-- title:
--   Unbounded-variation stopped scale harmonicity from a negative starting reserve
-- statement:
--   For any x<0 with x≤a, the exact strict two-sided stopped scale payoff equals W(x)=0 for an unbounded-variation spectrally negative Lévy process. The downward clock is zero at the initially ruined reserve, so the strict upper-before-lower discounted exit factor vanishes. The accepted terminal payoff factorisation gives the identity for any upper boundary a, including positive a. Infinite-clock and tie conventions remain exactly those of the canonical theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), arXiv:math/0702893. Independently Proved Prove2Me chat04_strict_exit_discount_zero_of_negative_reserve and chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_discount_zero_of_negative_reserve

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_stopped_scale_negative_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (hx : x < 0) :
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
      else 0) ∂P) = ENNReal.ofReal (W x) := by sorry
