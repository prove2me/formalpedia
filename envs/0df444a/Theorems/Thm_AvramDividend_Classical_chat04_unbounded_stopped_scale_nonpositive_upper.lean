-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_nonpositive_upper
-- name    : AvramDividend.Classical.chat04_unbounded_stopped_scale_nonpositive_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:26:59.848987+00:00
-- url     : https://prove2.me/theorems/6da3d7ac-6e5f-41c3-acba-b806abda2394
-- title:
--   Unbounded-variation stopped scale harmonicity for nonpositive upper barrier
-- statement:
--   For a spectrally negative Levy process of unbounded variation, q>0, a q-scale function W, and starting reserve x≤a≤0, the entire strict two-sided stopped discounted W payoff equals W(x). The weak-endpoint branch follows from the accepted payoff factorisation and the fact that W vanishes on (-infinity,0] in unbounded variation. This reduces the canonical general-reserve harmonicity parent to the positive-upper-barrier case.
-- source:
--   Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, scale-function support and unbounded-variation zero boundary. Prove2Me accepted strict terminal payoff factorisation and accepted scale zero origin.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem chat04_unbounded_stopped_scale_nonpositive_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (ha : a ≤ 0) :
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
end AvramDividend.Classical
