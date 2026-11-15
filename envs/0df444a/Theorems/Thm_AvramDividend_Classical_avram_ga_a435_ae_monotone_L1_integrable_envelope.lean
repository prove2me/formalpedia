-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a435_ae_monotone_L1_integrable_envelope
-- name    : AvramDividend.Classical.avram_ga_a435_ae_monotone_L1_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:05:54.706512+00:00
-- url     : https://prove2.me/theorems/d7651fc4-3ee8-45af-99f2-255209b383d5
-- title:
--   Uniform nonnegative L1 bounds imply integrable envelope for an a.e. measurable monotone sequence
-- statement:
--   A nonnegative pointwise increasing sequence of integrable random variables with a uniform expectation bound has an integrable common almost-everywhere envelope even without globally measurable representatives.
-- source:
--   Monotone convergence for a.e.-measurable extended nonnegative real sequences; Mathlib lintegral_iSup_prime and ae_lt_top_prime; direct extension of a429 to serve the a425 Gaussian dyadic sequence.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a435_ae_monotone_L1_integrable_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hint : ∀ k, Integrable (f k) P)
    (hnonneg : ∀ k ω, 0 ≤ f k ω)
    (hmono : ∀ ω, Monotone (fun k => f k ω))
    (hbudget : ∀ k, (∫ ω, f k ω ∂P) ≤ K) :
    ∃ S : Ω → ℝ, Integrable S P ∧
      ∀ᵐ ω ∂P, 0 ≤ S ω ∧ ∀ k, f k ω ≤ S ω := by sorry
