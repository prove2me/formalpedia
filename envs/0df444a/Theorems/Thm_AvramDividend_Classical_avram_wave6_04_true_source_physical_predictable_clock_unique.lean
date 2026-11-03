-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:17:35.360758+00:00
-- url     : https://prove2.me/theorems/0db576b1-f664-4d2a-b2b7-e570a3163857
-- title:
--   Original source physical-time predictable compensator clock has a unique restriction law
-- statement:
--   Any two measures on the original right-continuous predictable sigma-algebra which both equal the genuine deterministic physical finite-horizon real-time × source probability product on all predictable measurable sets must be identical. This makes hμclock canonical, but does not claim the still-Open source jump intensity law.
-- source:
--   Wave6 Chat04 source physical predictable time-clock uniqueness using Measure.ext and exact physical-time product equality, independent of Chat01.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
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
    μ₁ = μ₂ := by sorry
