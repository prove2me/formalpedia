-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_all_compact_horizons_ae_bounded
-- name    : AvramDividend.Classical.avram_ja18_intrinsic_gaussian_all_compact_horizons_ae_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:08:00.561856+00:00
-- url     : https://prove2.me/theorems/4fa8501b-7b07-4ba8-993e-d31e3ca5f7b7
-- title:
--   True physical Gaussian source is bounded on every compact time horizon almost surely
-- statement:
--   On one conull set the original spectrally negative Lévy physical intrinsic Gaussian residual is continuous on the whole nonnegative time axis and thus bounded on every finite time interval. This is the pathwise compact-maximum step required by the stronger integrable-maximal-source estimate, preserving the original source rather than an abstract Gaussian substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18_intrinsic_gaussian_all_compact_horizons_ae_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ B : ℝ,
      ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) → ‖R t ω‖ ≤ B := by sorry
