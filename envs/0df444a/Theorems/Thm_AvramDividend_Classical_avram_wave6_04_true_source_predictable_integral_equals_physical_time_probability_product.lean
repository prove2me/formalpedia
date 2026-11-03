-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_predictable_integral_equals_physical_time_probability_product
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_predictable_integral_equals_physical_time_probability_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:08:39.507812+00:00
-- url     : https://prove2.me/theorems/ed670337-962d-4b19-ad8a-ea39e069dd19
-- title:
--   Actual source predictable generator drift integral equals the original physical-time product integral
-- statement:
--   For the original filtered Lévy source and any strongly measurable integrand on the right-continuous predictable sigma-algebra, if μ agrees on all predictable sets with the real-time Lebesgue [0,T] × original source probability P clock, prove that integrating f against μ is exactly integrating f against the physical-time × P product. Use the source predictable-to-ambient inclusion and Mathlib integral_trim, not an invented compensated jump clock. This is the missing physical clock integral transport needed for Chat06's stopped discounted generator formula.
-- source:
--   Wave6 Chat04 accepted physical clock construction and pinned Mathlib integral_trim; physical-time integral, independent of still-Open Chat01 source jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_predictable_integral_equals_physical_time_probability_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (f : (ℝ≥0 × Ω) → ℝ)
    (hf : StronglyMeasurable[𝓕.rightCont.predictable] f) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω, f p ∂μ) =
      ∫ p : ℝ≥0 × Ω, f p
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by sorry
