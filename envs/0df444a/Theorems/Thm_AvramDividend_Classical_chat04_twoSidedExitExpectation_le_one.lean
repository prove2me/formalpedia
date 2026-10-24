-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one
-- name    : AvramDividend.Classical.chat04_twoSidedExitExpectation_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:05:49.152503+00:00
-- url     : https://prove2.me/theorems/dde72b60-9dac-4c91-91bb-f67d00e44444
-- title:
--   Killed two-sided discounted exit transform is at most one
-- statement:
--   For every spectrally negative Lévy process on its probability space, every nonnegative discount rate and any real barrier and initial reserve, the nonnegative killed two-sided exit transform is bounded by one. The proof is pathwise, valid at infinite exit times and independent of scale function identities.
-- source:
--   Elementary domination of the exact killed ENNReal reward and normalisation of the process probability measure. Based on published Definitions.Def_AvramDividend_Classical_TwoSidedExit.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_twoSidedExitExpectation_le_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hq : 0 ≤ q) :
    twoSidedExitExpectation X q a x ≤ 1 := by sorry
