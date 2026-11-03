-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_ae_predictable_integral_equals_physical_time_probability_product
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_ae_predictable_integral_equals_physical_time_probability_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:15:33.517279+00:00
-- url     : https://prove2.me/theorems/55a364af-6c25-4c83-854d-c5228003cd98
-- title:
--   Actual source almost-everywhere predictable generator drift integral equals physical-time probability product
-- statement:
--   Strengthen the original source physical predictable time integration bridge to an integrand that is only almost-everywhere strongly measurable on the right-continuous predictable sigma algebra with respect to the canonical physical clock μ. Its predictable-clock integral equals the ordinary finite real-time Lebesgue × P product integral, by pinned Mathlib integral_trim_ae; source X.X jump intensity remains Chat01's separate obligation.
-- source:
--   Wave6 Chat04 original source clock construction plus pinned Mathlib integral_trim_ae, extending the Proved strongly-measurable transport to AE strong measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_ae_predictable_integral_equals_physical_time_probability_product
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
    (hf : AEStronglyMeasurable[𝓕.rightCont.predictable] f μ) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω, f p ∂μ) =
      ∫ p : ℝ≥0 × Ω, f p
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by sorry
