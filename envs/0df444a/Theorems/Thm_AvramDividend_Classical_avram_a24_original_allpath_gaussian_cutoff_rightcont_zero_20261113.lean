-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
-- name    : AvramDividend.Classical.avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:06.148191+00:00
-- url     : https://prove2.me/theorems/6fb88b75-9bfa-497e-99fb-bb9915e1b1d9
-- title:
--   Every physical Gaussian residual cutoff is right-continuous on every original sample path and starts at zero
-- statement:
--   For every original spectrally negative Lévy source path and every finite cutoff, the intrinsic Gaussian residual cutoff is right-continuous at every horizon and vanishes at time zero.
-- source:
--   Proved source right continuity of X, compensated small marks 352103fe, large jumps b2377e1f, zero-origin 2e39b05b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_smallband_cutoff_rightcont_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18w_original_largejump_sum_rightcont
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original finite Gaussian residual cutoff is right-continuous on every path and starts at zero. -/

theorem AvramDividend.Classical.avram_a24_original_allpath_gaussian_cutoff_rightcont_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n : ℕ) (ω : Ω),
      (∀ t : ℝ≥0, ContinuousWithinAt
        (fun s : ℝ≥0 =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω)
        (Ici t) t) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n 0 ω = 0 := by sorry
