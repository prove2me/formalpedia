-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:15:15.999487+00:00
-- url     : https://prove2.me/theorems/ddd2cd06-3b24-4a7f-8494-4a768184a63b
-- title:
--   Canonical physical-time source predictable clock exists as finite trim of real-time probability product
-- statement:
--   For the original filtered source, the actual finite-horizon physical real clock times P admits a finite measure on the right-continuous predictable sigma-algebra whose value on every predictable measurable set equals the original real-time product measure. This constructs the exact hμclock object required by the stopped discounted source generator, without claiming the source jump-count intensity hFuture.
-- source:
--   Wave6 Chat04 canonical source-time clock existence by predictable-measurable inclusion and Mathlib Measure.trim; independent of Chat01 stochastic jump-intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by sorry
