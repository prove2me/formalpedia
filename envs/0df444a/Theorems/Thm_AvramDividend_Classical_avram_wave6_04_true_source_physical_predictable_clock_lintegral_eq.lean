-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_lintegral_eq
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_lintegral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:14:05.171086+00:00
-- url     : https://prove2.me/theorems/504eb909-ba1d-44ed-b7a7-e7e92cdb8d05
-- title:
--   True source finite predictable physical clock agrees with Lebesgue-time probability on all predictable lintegrals
-- statement:
--   For the original right-continuous filtered source, finite horizon and a measure μ on the predictable sigma algebra agreeing on predictable sets with physical [0,T] real time × P, show equality of ∫⁻ f dμ and the physical product ∫⁻ f for every predictable measurable nonnegative f. This supplies the exact clock lintegral hypothesis required by the already Proved source signed generator drift L1 theorem, without asserting the still-Open intrinsic X.X jump compensator law.
-- source:
--   Wave6 Chat04 physical clock trim construction with pinned Mathlib lintegral_trim; direct interface to c254b492 generator drift L1 theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_lintegral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (f : (ℝ≥0 × Ω) → ℝ≥0∞)
    (hf : Measurable[𝓕.rightCont.predictable] f) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫⁻ p : ℝ≥0 × Ω, f p ∂μ) =
      ∫⁻ p : ℝ≥0 × Ω, f p
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by sorry
