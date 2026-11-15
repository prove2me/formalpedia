-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a376_ae_integrable_three_term_expected_source_upper
-- name    : AvramDividend.Classical.avram_ga_a376_ae_integrable_three_term_expected_source_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:31:57.224195+00:00
-- url     : https://prove2.me/theorems/dc3010a9-3613-4492-8187-d45663b6c199
-- title:
--   AE upper bound by weighted integrable energy plus two integrable errors transfers to expected integral upper bound
-- statement:
--   When real source F is integrable and almost everywhere bounded by ε times integrable source E plus two integrable errors A,B, its expectation is bounded by the weighted expected energy and the expected errors. This is exact Bochner integral linearity and integral_mono_ae. It isolates the integral bookkeeping of original Gaussian small selected-threshold a364 and a361 for remote Lean compilation.
-- source:
--   Generic Bochner integral monotonicity and additivity; original Gaussian expected small Taylor cutoff a364.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a376_ae_integrable_three_term_expected_source_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E A B : Ω → ℝ) (ε : ℝ)
    (hFI : Integrable F P)
    (hEI : Integrable E P)
    (hAI : Integrable A P)
    (hBI : Integrable B P)
    (hPt : ∀ᵐ ω ∂P, F ω ≤ ε*E ω+A ω+B ω) :
    (∫ ω, F ω ∂P) ≤
      ε*(∫ ω, E ω ∂P) +
        (∫ ω, A ω ∂P) +
        (∫ ω, B ω ∂P) := by sorry
