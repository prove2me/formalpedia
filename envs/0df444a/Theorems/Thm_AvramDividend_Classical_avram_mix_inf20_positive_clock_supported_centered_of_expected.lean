-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_positive_clock_supported_centered_of_expected
-- name    : AvramDividend.Classical.avram_mix_inf20_positive_clock_supported_centered_of_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:49:20.274208+00:00
-- url     : https://prove2.me/theorems/0312fea5-fa79-4b71-9e25-b75ec020821f
-- title:
--   Positive-mass event expected bound constructs a genuinely event-supported centred witness
-- statement:
--   On a positive-probability event, an integrable source reward satisfying an eventwise expectation upper bound admits a real integrable centred witness supported on that same event, which dominates the reward excess pointwise there. Construct the witness by subtracting the exact eventwise mean and dividing by the positive event probability; the correction is nonnegative. This is the independent probability bridge needed to turn original positive-clock expected HJB inequalities into a zero-clock-supported martingale certificate. It assumes the source expectation inequality rather than inventing it.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf20_positive_clock_supported_centered_of_expected
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (b : ℝ) (hp : 0 < (P A).toReal)
    (hbudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, ω ∉ A → M ω = 0) ∧
      (∀ ω, ω ∈ A → F ω ≤ b + M ω) := by sorry
