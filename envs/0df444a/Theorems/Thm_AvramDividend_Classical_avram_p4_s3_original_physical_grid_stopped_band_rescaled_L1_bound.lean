-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_grid_stopped_band_rescaled_L1_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_grid_stopped_band_rescaled_L1_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:14:16.752894+00:00
-- url     : https://prove2.me/theorems/a7f4c4cd-1c03-48f6-bf2b-5c9ed4c19616
-- title:
--   Original physical-grid stopped negative-band jump count has uniform rescaled L1 intensity bound
-- statement:
--   For the actual original spectrally negative Levy path, any measurable sample-dependent clock τ_k bounded by T/k and positive grid k satisfies k times the expectation of its finite negative-band jump count at most (T:Real) times the original band Levy intensity. This supplies the exact source physical-grid first-moment budget for finite-band compensated-jump terms.
-- source:
--   The accepted original stopped-count first moment theorem 5e515f36 at physical horizon T/k and accepted exact real-rate conversion c3093fe5 yield k E Kτk≤k·(Tν(B)/k)=Tν(B), for positive k.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_grid_stopped_band_rescaled_L1_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0))
    (hKmeas : ∀ k, Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (k : ℕ) (hk : 0 < k) :
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
    (k : ℝ) * (∫ ω, (K ω : ℝ) ∂P) ≤
      (T : ℝ) * (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal := by sorry
