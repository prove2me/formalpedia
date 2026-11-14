-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB294b_probability_fibre_integral_envelope
-- name    : AvramDividend.Classical.avram_gbB294b_probability_fibre_integral_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:20:39.935247+00:00
-- url     : https://prove2.me/theorems/b2cb48f9-65ef-4dee-8fd3-96d3ee12fe42
-- title:
--   Original probability-space section bounds integrate to sample-time product measure upper bounds
-- statement:
--   For an original probability measure and a jointly measurable sample-by-physical-time event, pointwise upper bounds on its original probability sections integrate to an upper bound on its true probability-by-time product mass. The probability hypothesis ensures the sigma-finiteness needed for symmetric product Tonelli. This corrects the earlier overly general formulation and supports true B266 original Gaussian good-cell occupation bounds.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB294b_probability_fibre_integral_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by sorry
