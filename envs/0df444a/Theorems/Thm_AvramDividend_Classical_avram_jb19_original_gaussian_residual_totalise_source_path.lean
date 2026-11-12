-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb19_original_gaussian_residual_totalise_source_path
-- name    : AvramDividend.Classical.avram_jb19_original_gaussian_residual_totalise_source_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:57:12.558553+00:00
-- url     : https://prove2.me/theorems/561f5a08-5205-4000-ab2e-1a9d3c2c3ce6
-- title:
--   Total original Lévy source path decomposition with Gaussian residual equal almost everywhere
-- statement:
--   Given simultaneous almost-everywhere limits of the actual intrinsic Gaussian residual and compensated small-jump field, construct a modified Gaussian field on the same original sample space so that the exact Levy drift plus Gaussian, small-jump and large-jump decomposition holds for every sample path and every nonnegative time. The modification equals the original residual almost surely at all times, so it can be used in finite stopped Taylor meshes without changing integrals or conditional expectations.
-- source:
--   Proved ce29c6e1 original residual/jump path equality; bridge into Proved 62a48d60 and a5b511f4 exact finite-mesh algebra; prerequisite for the mixed stopped Ito ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb19_original_gaussian_residual_totalise_source_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ t ω, X.X t ω =
        (t : ℝ) * X.c + M t ω + Jsmall t ω +
          avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = R t ω) := by sorry
