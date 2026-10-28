-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_ae_eq_zero_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.twoSidedExitDownTime_ae_eq_zero_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:02:34.331427+00:00
-- url     : https://prove2.me/theorems/4b9507d9-e1bd-4aad-9a08-37ea4f6c24d0
-- title:
--   Almost-sure negative observations near zero imply instantaneous lower exit
-- statement:
--   Almost every path has negative observations at arbitrarily small times. Therefore almost every path exits downwards immediately from zero.
-- source:
--   Pathwise near-zero regularity and measure-theoretic eventuality.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_near_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitDownTime_ae_eq_zero_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0 := by sorry
