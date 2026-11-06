-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:10:46.235123+00:00
-- url     : https://prove2.me/theorems/b3b05dd5-bde3-4ccd-babb-9accc1b6bf8c
-- title:
--   Original stopped finite negative-band chronological jump-pair factorial moment bounded by squared physical intensity
-- statement:
--   For the original spectrally negative Levy path and arbitrary sample-dependent clock τ bounded by T, the factorial pair count Kτ(Kτ−1) of negative-band jumps is integrable and its expectation is at most the squared physical intensity r². This is an O(T²) bound on expected ordered jump collisions, directly useful for the original finite-grid source martingale and Taylor remainder.
-- source:
--   Accepted original finite marked-time count identity and exact deterministic first/second factorial moments; ncard monotonicity Kτ≤KT, monotonicity of k(k−1) on natural numbers, and dominated Bochner integrability. No process replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_band_count_factorial_moment_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2 := by sorry
