-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_rate_normalized_marks_to_levy_intensity
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_band_rate_normalized_marks_to_levy_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:26:13.053192+00:00
-- url     : https://prove2.me/theorems/692e71a5-41b8-4a46-9a69-02956c958552
-- title:
--   Finite-rate Poisson cell mean of normalized marks equals unnormalized Lévy compensator integral
-- statement:
--   For a finite-intensity mark band, if ρ is the probability mark law and ν = λ•ρ the original unnormalized Lévy intensity measure, prove (tλ)∫f dρ = t∫f dν for integrable signed f. This is the bridge between the genuine independent-count normalized mark formula and source-X generator compensator, derived solely from measure scaling rather than assuming compensation.
-- source:
--   Pinned Mathlib 0df444a MeasureTheory.Integral.Bochner.Basic integral_smul_measure and ring algebra.

import Mathlib

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_finite_band_rate_normalized_marks_to_levy_intensity
    {E : Type*} [MeasurableSpace E]
    (ν ρ : Measure E) [IsProbabilityMeasure ρ]
    (rate : ℝ≥0∞) (hrate : rate < ∞) (hν : ν = rate • ρ)
    (f : E → ℝ) (hf : Integrable f ρ)
    (t : ℝ) (ht : 0 ≤ t) :
    (t * rate.toReal) * ∫ z, f z ∂ρ =
      t * ∫ z, f z ∂ν := by sorry
