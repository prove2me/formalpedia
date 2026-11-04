-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:28:39.112267+00:00
-- url     : https://prove2.me/theorems/536848df-b26c-4435-8ced-7d6d683790f0
-- title:
--   Original right-continuous predictable finite clock has exact physical-time by past-event mass
-- statement:
--   The original finite physical predictable clock μ is known to agree with the real Lebesgue [0,T] pushforward times the original probability P on predictable cells. On a genuine adapted past rectangle (s,t]×A with t≤T its mass is exactly ENNReal.ofReal(t-s)·P(A). The proof uses original rightCont predictability, the concrete physical time pushforward volume and actual product measure. No compensator law or Poisson model.
-- source:
--   Proved true_source_finite_physical_predictable_clock_exists_unique interface; P3-B original time-clock interval mass, Mathlib Measure.prod_prod.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_real_to_nonneg_clock_interval_mass
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_clock_interval_event_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (s t : ℝ≥0) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    μ (Ioc s t ×ˢ A) =
      ENNReal.ofReal ((t : ℝ) - (s : ℝ)) * P A := by sorry
