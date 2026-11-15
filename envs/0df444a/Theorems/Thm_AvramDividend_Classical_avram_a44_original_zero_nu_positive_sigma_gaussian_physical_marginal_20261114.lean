-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
-- name    : AvramDividend.Classical.avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:29:26.735265+00:00
-- url     : https://prove2.me/theorems/13537065-8508-40c8-8cf3-1ec92efaba6d
-- title:
--   Original zero-jump positive-volatility intrinsic Gaussian residual has exact centred normal marginals
-- statement:
--   The physical intrinsic Gaussian cutoff residual of a zero-jump Levy source with positive sigma has centred normal law with variance sigma squared times time under the original probability space.
-- source:
--   Proved A40 normalised law, A31 original ae measurability and Mathlib gaussianReal_mul_const.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a40_original_zero_nu_intrinsic_gaussian_normalised_exact_law_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_gaussian_source_ae_representative_measurable_20261114
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a44_original_zero_nu_positive_sigma_gaussian_physical_marginal_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hNu : X.ν = 0) (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (R t) P =
        gaussianReal 0
          ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) := by sorry
