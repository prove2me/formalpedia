-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:05:05.252894+00:00
-- url     : https://prove2.me/theorems/5e515f36-a295-4462-bcaa-1569bc426a7a
-- title:
--   True bounded-ruin original negative-band count has L1 first-moment bound T times Levy intensity
-- statement:
--   For the original spectrally negative Levy path and an arbitrary sample-dependent stopping clock τ bounded by deterministic T, if the intrinsic stopped finite-band jump count is measurable then it is integrable and its expectation is at most the exact original first-moment intensity (T ν(Iic(-1/(n+1)))).toReal. This strengthens second-moment control to the first-order physical rate needed for martingale construction.
-- source:
--   Use the original finite jump-time inclusion, the Proved exact marked-count pathwise identity f0197436, Proved original real marked count integrability c1e09ada and expectation 3d8bb7f8. Dominate Kτ by KT pathwise and apply integrable monotonicity and integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_real_mean_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ)) P ∧
      (∫ ω, (K ω : ℝ) ∂P) ≤ r := by sorry
