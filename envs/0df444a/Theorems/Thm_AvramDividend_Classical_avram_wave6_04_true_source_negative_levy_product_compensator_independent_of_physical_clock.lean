-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_negative_levy_product_compensator_independent_of_physical_clock
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_compensator_independent_of_physical_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:40:53.630962+00:00
-- url     : https://prove2.me/theorems/16f477e7-dca5-404f-b76b-edd6fb07d1dd
-- title:
--   True source negative Lévy compensator product is canonical across finite physical predictable clocks
-- statement:
--   For the actual original spectrally negative Lévy source X and filtration, any two predictable measures that coincide with its physical real-time × probability clock give exactly the same negative-mark product compensator μ.prod (X.ν.restrict (-∞,0)). This source-specific uniqueness removes dependence on the representation of μ while retaining the independent Chat 01 obligation that intrinsic X.X jumps have this intensity.
-- source:
--   Wave6 Chat04 actual original X.ν compensator identity using the newly accepted physical predictable clock uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_compensator_independent_of_physical_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (μ₁ μ₂ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ₁ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₁ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hμ₂ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₂ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     μ₁.prod (X.ν.restrict (Iio (0 : ℝ)))) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     μ₂.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
