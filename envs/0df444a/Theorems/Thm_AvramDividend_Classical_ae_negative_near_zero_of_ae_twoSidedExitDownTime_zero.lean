-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_ae_twoSidedExitDownTime_zero
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_ae_twoSidedExitDownTime_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:15:31.786879+00:00
-- url     : https://prove2.me/theorems/bc92727d-cd4a-4b78-b607-d082a367bf95
-- title:
--   Almost-sure instantaneous lower passage implies negative observations arbitrarily close to zero
-- statement:
--   An almost surely zero strict negative first-passage clock implies that almost every path has the corresponding strict crossing in every positive time interval.
-- source:
--   Pathwise iInf zero-time converse and monotonicity of almost-everywhere predicates.

import Theorems.Thm_AvramDividend_Classical_negative_near_zero_of_twoSidedExitDownTime_zero
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_ae_twoSidedExitDownTime_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h0 : ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
