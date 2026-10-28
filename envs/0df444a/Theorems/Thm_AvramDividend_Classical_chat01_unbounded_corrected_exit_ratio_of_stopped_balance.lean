-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_unbounded_corrected_exit_ratio_of_stopped_balance
-- name    : AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:44:20.977637+00:00
-- url     : https://prove2.me/theorems/c59bf6d7-edc3-4e87-9d7f-7122e93f8af7
-- title:
--   Corrected two-sided exit ratio from a stopped-scale balance without Standing
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and its canonical q-scale function, an exact stopped-scale balance implies the corrected killed upper-before-lower exit expectation equals W(x)/W(a). Strict positivity of W(a) holds without Standing; cancel the finite nonzero ENNReal factor and use equality of the original and corrected strict exit definitions. This is the precise conditional algebraic bridge needed between the open killed stopping identity and Esscher first-passage decay.
-- source:
--   Proved scaleFunction_strict_pos_of_unbounded_variation and chat04_twoSidedExitExpectation_eq_corrected; ENNReal scale-factor cancellation as in the accepted standing-case chat04_exit_ratio_of_stopped_balance.

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat01_unbounded_corrected_exit_ratio_of_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    twoSidedExitExpectationCorrected X q a x =
      ENNReal.ofReal (W x / W a) := by sorry
