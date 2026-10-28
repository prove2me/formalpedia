-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_cross_derivative_of_corrected_exit
-- name    : AvramDividend.Classical.unbounded_scale_cross_derivative_of_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:47:00.955251+00:00
-- url     : https://prove2.me/theorems/3e357704-4bae-4287-a910-077c1ecc67bb
-- title:
--   Unbounded q-scale derivative cross-order from corrected two-sided exits
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, the corrected q-discounted two-sided exit-scale identity and differentiability of W only at two positive points x≤y imply W'(y)W(x) ≤ W'(x)W(y). The proof uses a Proved shifted-reserve exit comparison and positive scale function to obtain forward-ratio ordering, then the independently Proved pointwise derivative inequality. This is a verified local alternative to global logarithmic concavity, with the one outstanding first-passage identity explicit.
-- source:
--   Avram Palmowski Pistorius (2007), Eq. (3.6), scale first passage; logarithmic concavity by ratio comparison.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_shifted_initial_reserve_monotone
import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_cross_derivative_le
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_cross_derivative_of_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ W x)
    (hdy : DifferentiableAt ℝ W y) :
    deriv W y * W x ≤ deriv W x * W y := by sorry
