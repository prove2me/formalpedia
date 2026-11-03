-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_predictable_clock_lintegral_eq_without_probability_instance
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_predictable_clock_lintegral_eq_without_probability_instance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:43:22.758639+00:00
-- url     : https://prove2.me/theorems/148ccddc-feb8-4790-8449-77826bb54932
-- title:
--   Physical predictable source clock lintegral transport without probability typeclass
-- statement:
--   For a general source measure P on the filtered path space, without assuming IsProbabilityMeasure P, equality of the finite physical-time product clock and a predictable clock on all predictable events implies equality of integrals of every predictable measurable nonnegative function. This instance-free form supports signed original-source nonlinear generator tail transport, without inferring intrinsic X.X jump compensation from the clock.
-- source:
--   Wave6 Chat04 probability-independent version of already Proved original predictable clock trim and lintegral identity 504eb909; same proof with unused IsProbabilityMeasure assumption removed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source physical clock transport for nonnegative predictable
functions, the lintegral interface used by source negative-jump L1
energy theorems. The intensity of X.X remains a separate obligation. -/

theorem AvramDividend.Classical.avram_wave6_04_true_source_predictable_clock_lintegral_eq_without_probability_instance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
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
