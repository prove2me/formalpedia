-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
-- name    : AvramDividend.Classical.avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:17:30.932933+00:00
-- url     : https://prove2.me/theorems/e571626c-7a46-4300-b50e-a74f45464d09
-- title:
--   Original finite-activity intrinsic Gaussian source limit has globally continuous physical sample paths on one conull event
-- statement:
--   Under original finite-negative-activity Lévy source standing assumptions, the actual intrinsic Gaussian cutoff residual limit has continuous sample paths at all nonnegative times simultaneously on one original-probability event of probability one.
-- source:
--   A36 original physical finite-horizon Gaussian source continuity and A37 deterministic localisation to global continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a38_original_intrinsic_gaussian_physical_limit_globally_continuous_ae_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => R t ω) := by sorry
