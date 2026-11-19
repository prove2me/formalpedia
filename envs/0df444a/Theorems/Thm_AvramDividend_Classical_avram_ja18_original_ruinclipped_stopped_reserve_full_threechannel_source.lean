-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
-- name    : AvramDividend.Classical.avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:36:17.029363+00:00
-- url     : https://prove2.me/theorems/85c316b5-3317-45ee-82d9-b438cc5245cb
-- title:
--   Full original stopped reserve physical three-channel Gaussian-small-large mark source at ruin contact
-- statement:
--   For the genuine original spectrally negative Levy process and original dividend strategy at any random clock τ, its right-payment/postruin stopped reserve is exactly original initial capital plus original drift, intrinsic Gaussian residual limit, compensated small-negative-mark limit and uncompensated large-negative-mark sum, minus the correct right-limit dividend payment if strictly pre-ruin or usual dividend otherwise. This simultaneous a.e. source ledger retains the original physical ruin-contact branch and all negative-mark channels. It is a direct replacement starting point for the Open finite mixed stopped Ito cash majorant, avoiding a synthetic jump witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_ruinclipped_stopped_reserve_full_threechannel_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, W ω =
      x + (τ ω : ℝ) * X.c + R (τ ω) ω + Jsmall (τ ω) ω +
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω -
      (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
       then rightLimit D (τ ω) ω else D (τ ω) ω) := by sorry
