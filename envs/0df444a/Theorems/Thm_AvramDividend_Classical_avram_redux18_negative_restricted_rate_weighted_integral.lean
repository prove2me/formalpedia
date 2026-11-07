-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_negative_restricted_rate_weighted_integral
-- name    : AvramDividend.Classical.avram_redux18_negative_restricted_rate_weighted_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:02:40.287882+00:00
-- url     : https://prove2.me/theorems/14e02b4e-0749-42a8-a9b8-a17a82447799
-- title:
--   Negative Borel-band rate agreement determines all nonnegative weighted mark integrals
-- statement:
--   If two sigma-additive mark-rate measures agree on every Borel sub-band of a given measurable negative-jump band B, their restrictions to B agree, so the integrals of every nonnegative extended-real mark weight over B coincide. This exact measure-uniqueness bridge converts the original intrinsic markRate in the Proved weighted Campbell identity into the original Lévy measure ν using the Proved negative-Borel rate identity.
-- source:
--   Measure.ext on the restrictions, using Measure.restrict_apply on C∩B and the measurable-set equality hypothesis, then rewrite the restricted lintegral by the measure equality.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_negative_restricted_rate_weighted_integral
    (μ ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hEq : ∀ C : Set ℝ, MeasurableSet C → C ⊆ B → μ C = ν C)
    (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in B, g y ∂μ) = (∫⁻ y in B, g y ∂ν) := by sorry
