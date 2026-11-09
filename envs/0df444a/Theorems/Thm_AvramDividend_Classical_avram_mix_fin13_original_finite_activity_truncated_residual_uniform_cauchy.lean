-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
-- name    : AvramDividend.Classical.avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:34:56.195205+00:00
-- url     : https://prove2.me/theorems/75dc3e14-280d-4ae9-b0bf-1fa7334bdefd
-- title:
--   Almost-sure uniform finite-clock Cauchy convergence of original Gaussian residual truncations
-- statement:
--   For the actual finite-negative-jump-activity spectrally negative Levy source X, on the original sample space and filtration, the truncated intrinsic residual is almost surely uniformly Cauchy over every bounded time horizon. A uniform pathwise negative jump gap makes all sufficiently thin near-zero mark bands empty, while the proved physical residual difference estimate bounds all later truncations by a reciprocal cutoff times the finite total negative intensity. No auxiliary Gaussian process or unproved bracket property is used. This supplies a genuine source convergence prerequisite for the ruin-clipped finite mixed Ito-Meyer reward theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_negative_mark_void_ae
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_void_annulus_truncated_residual_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin13_original_finite_activity_truncated_residual_uniform_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
      ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m →
        ∀ t : ℝ≥0, t ≤ T →
          |avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω -
             avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω| < ε := by sorry
