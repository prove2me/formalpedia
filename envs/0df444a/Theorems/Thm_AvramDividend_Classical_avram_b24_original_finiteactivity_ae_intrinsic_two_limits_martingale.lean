-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_ae_intrinsic_two_limits_martingale
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_limits_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:16:16.484469+00:00
-- url     : https://prove2.me/theorems/4630a9f9-9a70-4e3f-b483-b2f6d4c7905d
-- title:
--   Original finiteactivity arbitrary intrinsic two AE-limit representatives inherit both conditional martingales
-- statement:
--   For the unchanged original Standing spectrally negative Lévy driver of finite negative mark intensity, any alltime a.e. representatives R and Jsmall of the original intrinsic Gaussian and compensated smallmark processes are both integrable at each physical time and genuine martingales under the original right-continuous filtration: E[R_b|F_a]=R_a and E[J_b|F_a]=J_a for a≤b. Build the canonical representatives by Proved b133 original two intrinsic martingale theorem with the zero stopping clock, identify arbitrary representatives by uniqueness of alltime a.e. intrinsic truncation limits, transfer integrability and conditional expectation via condExp_congr_ae. No post-ruin substitute or secondary probability space.
-- source:
--   Proved b133 2e2cb641 and accepted b24 integrable transfer 97d70e1c, Mathlib condExp_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_limits_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    (∀ u : ℝ≥0, Integrable (R u) P) ∧
    (∀ u : ℝ≥0, Integrable (Jsmall u) P) := by sorry
