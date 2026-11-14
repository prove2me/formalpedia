-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
-- name    : AvramDividend.Classical.avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:22:00.047198+00:00
-- url     : https://prove2.me/theorems/c554582e-25a1-44a5-aac8-d812acdafc30
-- title:
--   Generic positive measurable submask preserves integrability and vanishing expected source energy
-- statement:
--   For any measurable nonnegative finite observed source terms, restricting an integrable prefix mask to a measurable submask preserves integrability, and if the expected prefix sums vanish, so do those of the submask. This rigorously transfers original stopped Gaussian prefix second-energy and quadratic cross bounds to the actual physically full pre-stop cell mask in a169.
-- source:
--   Finite sum indicator monotonicity, integrable domination, monotone integral and squeeze; supports original full-cell Gaussian correction.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ)
    (A B : ℕ → ℕ → Ω → Prop)
    [∀ m i, DecidablePred (A m i)] [∀ m i, DecidablePred (B m i)]
    (f : ℕ → ℕ → Ω → ℝ)
    (hBA : ∀ m i ω, B m i ω → A m i ω)
    (hfNonneg : ∀ m i ω, 0 ≤ f m i ω)
    (hfMeas : ∀ m i, Measurable (f m i))
    (hBMeas : ∀ m i, MeasurableSet {ω : Ω | B m i ω})
    (hAI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if A m i ω then f m i ω else 0) P)
    (hALim : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if A m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, if B m i ω then f m i ω else 0) P) ∧
    Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, if B m i ω then f m i ω else 0) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
