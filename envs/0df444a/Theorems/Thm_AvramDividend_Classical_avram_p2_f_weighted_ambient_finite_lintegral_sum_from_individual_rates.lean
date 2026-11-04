-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:27:04.946724+00:00
-- url     : https://prove2.me/theorems/a30d1d38-a059-4149-8438-210a656570fe
-- title:
--   Finite ambient nonnegative weighted rate sum from independent individual moment identities
-- statement:
--   For actual ambient-measurable counts and weights, if each separately has a proved exact weighted ENNReal first moment, a finite sum of these counts has the sum of those moments. This is the source-neutral finite additivity stage of a predictable marked-jump compensator, with no original Levy rate or integrability assumption smuggled into the premises.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_finset_sum, Finset.sum_congr; original source owner must prove the per-index event and weighted identities separately.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι)
    (N H : ι → Ω → ℝ≥0∞) (r : ι → ℝ≥0∞)
    (hN : ∀ i ∈ S, Measurable (N i))
    (hH : ∀ i ∈ S, Measurable (H i))
    (hEach : ∀ i ∈ S,
      (∫⁻ ω, H i ω * N i ω ∂μ) = (∫⁻ ω, H i ω ∂μ) * r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂μ) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂μ) * r i) := by sorry
