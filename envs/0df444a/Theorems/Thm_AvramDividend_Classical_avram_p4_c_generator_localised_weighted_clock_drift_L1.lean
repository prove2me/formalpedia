-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_localised_weighted_clock_drift_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:29:06.910199+00:00
-- url     : https://prove2.me/theorems/cf007d27-ef1b-4380-8860-afcf4a88c3bc
-- title:
--   Discounted original ν-large jump drift is L1 on measurable stopped region under a local reserve cap
-- statement:
--   Under a finite observation clock, original spectrally-negative Lévy ν large-tail drift and bounded measurable clock discount a, the stopped-region-indicated drift is time-L1 provided the reserve is capped only where the region holds. Measurably clip reserve outside the stopped region to zero, apply previously Proved source clock_large_mark_drift_L1 and Mathlib Integrable.bdd_mul, then use indicator integrability. No stochastic compensation or endpoint generator evaluation is assumed.
-- source:
--   Accepted P4-C avram_p4_c_generator_clock_large_mark_drift_L1 (74e75601-8d54-47c3-9089-68391aac8273); Mathlib Integrable.bdd_mul, Integrable.indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_clock_large_mark_drift_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_localised_weighted_clock_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R a : T → ℝ) (hR : Measurable R) (ha : Measurable a)
    (A : Set T) (hA : MeasurableSet A)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t ∈ A, R t ∈ Icc 0 v)
    (M : ℝ) (hweight : ∀ t, |a t| ≤ M) :
    Integrable
      (A.indicator (fun t : T =>
        a t * ∫ z : ℝ, w (R t + z) - w (R t)
          ∂(X.ν.restrict (Iio (-ε))))) μ := by sorry
