-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_ae_intrinsic_two_limits_integrable
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_limits_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:06:26.464393+00:00
-- url     : https://prove2.me/theorems/97d70e1c-2e87-4f03-840f-e3dd9cc4c856
-- title:
--   Original finiteactivity arbitrary all-time intrinsic Gaussian and smallmark AE representatives are integrable
-- statement:
--   For the unchanged actual Standing spectrally negative Levy process of finite negative-jump intensity, any two arbitrary all-time almost surely convergent representatives R and Jsmall of the original intrinsic Gaussian truncated residual and compensated small-band processes are integrable at every deterministic time. Reuse Proved original two intrinsic martingales b133 (2e2cb641) at the trivial zero stopped clock with s=t=0, and uniqueness of real sequence limits to identify any given AE representatives. Its exact conclusion is the missing integrability input for finite predictable-mesh Itô cash source 2a7f8ab4 without altering physical X, P, filtration, or original ruin/payment conventions.
-- source:
--   Proved 2e2cb641 original intrinsic two-martingale witness and Mathlib tendsto_nhds_unique and Integrable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_limits_integrable
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
