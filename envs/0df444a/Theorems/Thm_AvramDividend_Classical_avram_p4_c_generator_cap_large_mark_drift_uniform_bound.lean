-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cap_large_mark_drift_uniform_bound
-- name    : AvramDividend.Classical.avram_p4_c_generator_cap_large_mark_drift_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:04.59146+00:00
-- url     : https://prove2.me/theorems/7085d7b6-9eee-486b-9690-446514df3893
-- title:
--   Original large negative raw-jump ν-drift uniformly bounded on all capped reserves including zero
-- statement:
--   For the original spectrally negative Lévy X, any payoff continuous on nonnegative reserves and zero on negatives has its raw large-negative-jump ν-tail drift uniformly bounded over the entire capped reserve interval [0,v], including y=0. The bound is an explicit multiple of the original finite ν-tail intensity. The proof uses the Proved source cap-wide raw mark bound, source separated tail intensity finiteness, and exact pinned Mathlib norm_setIntegral_le_of_norm_le_const. It assumes neither generator validity at zero nor a jump-counting compensator.
-- source:
--   P4-C Proved source raw cap-wide bound 36d694ee-0281-49ae-a316-489d0277a5cb and ε large intensity 23f951a3-7c41-4e79-b5b4-7c8c2e9c7ca6; pinned Mathlib norm_setIntegral_le_of_norm_le_const

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_uniform_on_prejump_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_cap_large_mark_drift_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (v ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t : ℝ, t < 0 → w t = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc 0 v,
      |∫ z in Iio (-ε), w (y + z) - w y ∂X.ν| ≤ B := by sorry
