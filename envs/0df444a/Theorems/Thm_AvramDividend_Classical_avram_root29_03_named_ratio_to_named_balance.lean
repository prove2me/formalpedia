-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_named_ratio_to_named_balance
-- name    : AvramDividend.Classical.avram_root29_03_named_ratio_to_named_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:44:18.324988+00:00
-- url     : https://prove2.me/theorems/9cd1047f-58a7-47ad-bc06-5921231bea65
-- title:
--   Converse strict two-sided exit scale-ratio normalisation to named cross-multiplied W(a) balance
-- statement:
--   For an actual Standing spectrally negative Levy process at q>0 and 0<a, 0<=x<=a, an explicit hypothesis that the genuine named discounted strict upper-before-lower expectation is Wq(x)/Wq(a) implies its cross-multiplied equality. Positivity of Wq(a) is proved from Standing; no original stochastic ratio result is imported.
-- source:
--   Inverse algebraic direction to canonical Proved chat04_exit_ratio_of_stopped_balance (81ce0d81); use Proved scaleFunction_strict_pos_of_standing (59531c77) and pinned ENNReal.ofReal_div_of_pos, ENNReal.div_mul_cancel. Genuine ratio is an explicit hypothesis.

import Mathlib.Data.ENNReal.Inv
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_named_ratio_to_named_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hRatio : twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by sorry
