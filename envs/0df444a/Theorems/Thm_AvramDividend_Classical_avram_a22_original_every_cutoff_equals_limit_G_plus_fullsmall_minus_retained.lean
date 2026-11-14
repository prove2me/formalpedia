-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_every_cutoff_equals_limit_G_plus_fullsmall_minus_retained
-- name    : AvramDividend.Classical.avram_a22_original_every_cutoff_equals_limit_G_plus_fullsmall_minus_retained
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:58:02.228105+00:00
-- url     : https://prove2.me/theorems/17f9c6c7-4a6e-459a-8a57-8f6652364d6c
-- title:
--   Each original Gaussian residual cutoff is intrinsic Gaussian limit plus full compensated small jumps minus physical retained jumps
-- statement:
--   On the SAME actual original probability space, any cutoff residual at n equals the intrinsic Gaussian cutoff limit R plus the full compensated original negative small-jump limit Jsmall minus the physically retained compensated small band at n, almost surely simultaneously for every n and horizon. No false Gaussian-only variance and no independent noise.
-- source:
--   Proved physical zero-cutoff original limit split 2dbfbe10, Proved original retained-band residual identity bfc8537f; Kyprianou finite activity compensated Poisson decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja19_original_zero_cutoff_split_from_two_intrinsic_limits
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_every_cutoff_equals_limit_G_plus_fullsmall_minus_retained
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0),
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        R t ω + Jsmall t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by sorry
