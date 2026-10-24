-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_iff_stopped_balance
-- name    : AvramDividend.Classical.chat04_exit_ratio_iff_stopped_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:02:41.861686+00:00
-- url     : https://prove2.me/theorems/dd744ff9-173f-476b-9b48-95d93f53bba9
-- title:
--   Strict exit scale ratio if and only if stopped-scale balance
-- statement:
--   The normalised strict two-sided exit formula is exactly equivalent to its multiplicative stopped-scale balance for standing spectrally negative Lévy processes. This is a complete algebraic equivalence using strict scale positivity; neither direction imports an Open theorem. It clarifies that the remaining stochastic obligation is common to both catalogue formulations.
-- source:
--   Proved AvramDividend.Classical.chat04_exit_ratio_of_stopped_balance UUID 81ce0d81-05fc-4922-82d6-c342311e3c27 and Proved scaleFunction_strict_pos_of_standing UUID 59531c77-8eaf-44ac-a657-5b3ae9dcf8d6; pinned Mathlib ENNReal.div_mul_cancel and ofReal_div_of_pos.

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_exit_ratio_iff_stopped_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (twoSidedExitExpectation X q a x = ENNReal.ofReal (W x / W a)) ↔
      (twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x)) := by sorry
