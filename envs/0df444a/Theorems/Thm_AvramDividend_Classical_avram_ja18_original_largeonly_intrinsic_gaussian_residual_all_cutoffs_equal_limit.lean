-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largeonly_intrinsic_gaussian_residual_all_cutoffs_equal_limit
-- name    : AvramDividend.Classical.avram_ja18_original_largeonly_intrinsic_gaussian_residual_all_cutoffs_equal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:28:39.040198+00:00
-- url     : https://prove2.me/theorems/90d16c3b-1bce-4e3b-92bd-f335efb7b4bc
-- title:
--   Original large-only negative-jump Gaussian intrinsic residual is exactly cutoff invariant at every time
-- statement:
--   For the original same-X Levy source with no small negative marks and a.s. jumps either zero or <= -1, the intrinsic Gaussian residual at every finite cutoff n equals the intrinsic limiting Gaussian process R at all times on one conull set. This follows by the already Proved finite-cutoff omitted-tail identity and original mark-source zero results. It upgrades a finite mesh statement to a simultaneous pathwise Gaussian source identity without artificial witness processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_b28_original_no_small_negative_jump_limit_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_largeonly_intrinsic_gaussian_residual_all_cutoffs_equal_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνsmall : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω = R t ω := by sorry
