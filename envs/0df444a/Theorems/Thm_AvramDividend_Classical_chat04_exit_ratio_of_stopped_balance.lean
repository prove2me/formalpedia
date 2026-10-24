-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance
-- name    : AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:53:39.495851+00:00
-- url     : https://prove2.me/theorems/81ce0d81-05fc-4922-82d6-c342311e3c27
-- title:
--   Strict two-sided exit ratio from a stopped-scale balance
-- statement:
--   Given the exact stopped-scale balance for a strict upper exit before ruin, the two-sided discounted exit expectation equals W(x)/W(a). The balance is an explicit hypothesis, so this is a fully provable algebraic bridge independent of any Open theorem. Strict positivity of W(a) follows from the published standing scale-function theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), two-sided exit identity. This declaration isolates the algebraic cancellation in the candidate for target 5bcf90e1 and makes the stochastic input an explicit hypothesis. Original source verified at SHA-256 e535d3933622a8afa9ddb76a7bc9383c26f6d1839718d3422c9ddff39cd68d85. Revision 2 repairs the first publication compiler error by importing MeasureSpaceDef and Filtration and opening MeasureTheory.

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBalance :
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) :
    twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a) := by sorry
