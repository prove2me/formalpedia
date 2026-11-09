-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_bounded_stop_uniform_count_L2
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_bounded_stop_uniform_count_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:13:58.701566+00:00
-- url     : https://prove2.me/theorems/5e586113-490c-4db7-ad6e-e788c0d2c19c
-- title:
--   Uniform finite-activity original stopped negative-jump count L2 bound
-- statement:
--   For any physical random clock bounded by T, whose original negative-jump count is measurable, and finite total negative Levy activity, the stopped original jump count has an integrable square with expectation at most R squared plus R where R is T times the total negative Levy intensity. The bound is independent of the cutoff and the stopping clock, suitable for physical stopped-source moment control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_square_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_bounded_stop_uniform_count_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
      (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ R ^ 2 + R := by sorry
