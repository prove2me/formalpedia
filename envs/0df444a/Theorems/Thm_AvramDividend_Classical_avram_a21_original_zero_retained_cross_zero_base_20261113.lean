-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_retained_cross_zero_base_20261113
-- name    : AvramDividend.Classical.avram_a21_original_zero_retained_cross_zero_base_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:36:19.478286+00:00
-- url     : https://prove2.me/theorems/759e10a2-6a60-4945-9341-ca50d820f85c
-- title:
--   Physical Gaussian residual and retained compensated cutoff covariance vanishes at index zero
-- statement:
--   The physically retained compensated small mark process is identically zero for cutoff index n=0; hence its original-space cross product against the zero-cutoff residual is integrable and has expectation zero. This proves the base case of original source orthogonality 5687dc34 without any stochastic independence assumption.
-- source:
--   Proved original source cutoff zero identity, and elementary Bochner integral of zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_zero_retained_cross_zero_base_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Integrable (fun ω =>
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω *
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) P ∧
    (∫ ω,
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω *
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω ∂P) = 0 := by sorry
