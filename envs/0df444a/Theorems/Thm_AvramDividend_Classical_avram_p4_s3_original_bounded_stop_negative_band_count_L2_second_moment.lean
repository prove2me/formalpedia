-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L2_second_moment
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L2_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:35:07.947886+00:00
-- url     : https://prove2.me/theorems/fb49a200-092d-4f9b-a23d-8eebd74e8bb8
-- title:
--   True stopped negative-band original jump count has L2 second moment bounded by r squared plus r
-- statement:
--   For the true original spectrally negative Levy process and every sample-dependent bounded stopping clock, the separated negative-band jump count is square-integrable, with E[K²] ≤ r²+r, where r is the physical deterministic horizon times the original Lévy band intensity. This is the exact compound-Poisson L² envelope needed for stopped finite-band sums.
-- source:
--   Combine Proved source-exact original stopped first moment 5e515f36 and factorial pair second moment b3b05dd5 via the pointwise ring identity K²=K(K−1)+K, Bochner integrability and linearity of the integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_count_L2_second_moment
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
    Integrable (fun ω => (K ω : ℝ) ^ 2) P ∧
    (∫ ω, (K ω : ℝ) ^ 2 ∂P) ≤ r ^ 2 + r := by sorry
