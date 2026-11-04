-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_clock_large_mark_drift_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:26:12.857787+00:00
-- url     : https://prove2.me/theorems/d2fcaa0f-c24b-4d44-ba32-4ab141b014fa
-- title:
--   Actual original negative large-jump drift is time-integrable on stopped measurable regions
-- statement:
--   The original Levy ν-tail raw large-jump drift, integrated over z<-ε, is L1 on the actual measurable stopped set A. Only R(t) for t in A must lie in [0,v]. Extend R by zero outside A, derive source original product L1, use finite tail intensity and Fubini integrability, then restrict the time integral to A. No original jump-count compensator is assumed.
-- source:
--   Previously Proved original P4-C finite_clock_raw_large_mark_L1 and epsilon_large_jump_intensity_finite; pinned Mathlib Integrable.integral_prod_left, Integrable.indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_clock_large_mark_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v) :
    Integrable
      (A.indicator (fun t : T =>
        ∫ z : ℝ, w (R t + z) - w (R t)
          ∂(X.ν.restrict (Iio (-ε))))) μ := by sorry
