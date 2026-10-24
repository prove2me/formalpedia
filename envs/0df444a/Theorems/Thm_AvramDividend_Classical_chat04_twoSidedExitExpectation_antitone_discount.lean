-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
-- name    : AvramDividend.Classical.chat04_twoSidedExitExpectation_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:07:08.81981+00:00
-- url     : https://prove2.me/theorems/69a4a254-000a-4139-880d-577bc9fca961
-- title:
--   Killed strict two-sided exit transform decreases with the discount rate
-- statement:
--   For any real discount rates q₁≤q₂ and any upper boundary and initial reserve, the killed two-sided exit expectation at q₂ is no larger than that at q₁. This follows pathwise because the first-passage time is nonnegative, with the strict upward-before-downward event held fixed.
-- source:
--   Direct discounted-reward comparison for the published strict killed two-sided exit transform; no scale identity or optional sampling required.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_twoSidedExitExpectation_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ a x := by sorry
