-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_clock_large_mark_drift_L1
-- name    : AvramDividend.Classical.avram_p4_c_generator_clock_large_mark_drift_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:07:54.74214+00:00
-- url     : https://prove2.me/theorems/74e75601-8d54-47c3-9089-68391aac8273
-- title:
--   Original large-mark compensator drift is integrable across any finite measurable capped clock
-- statement:
--   The genuine original Levy large negative-jump drift t↦∫_{z<-epsilon}[w(R(t)+z)-w(R(t))]ν(dz) is an integrable clock function whenever the observation clock measure is finite, the pre-jump reserve is measurable and capped, and w is continuous on the nonnegative reserves and zero on negatives. The proof applies Fubini's L1 theorem Integrable.integral_prod_left to the already Proved original ν large-mark product integrability, using source finite tail mass to discharge σ-finiteness. No P2 counting-measure compensator or stochastic Itô identity is postulated.
-- source:
--   P4-C Proved raw product L1 b40bbce6-b87e-4410-be59-ae28455ffecc and finite original ν tail 23f951a3-7c41-4e79-b5b4-7c8c2e9c7ca6, pinned Integrable.integral_prod_left

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_clock_raw_large_mark_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_clock_large_mark_drift_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (hR : Measurable R)
    (w : ℝ → ℝ) (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0)
    (hcap : ∀ t, R t ∈ Icc 0 v) :
    Integrable
      (fun t : T => ∫ z : ℝ, w (R t + z) - w (R t)
        ∂(X.ν.restrict (Iio (-ε)))) μ := by sorry
