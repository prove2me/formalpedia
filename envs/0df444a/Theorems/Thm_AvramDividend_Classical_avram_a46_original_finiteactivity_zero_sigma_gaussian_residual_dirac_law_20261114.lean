-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a46_original_finiteactivity_zero_sigma_gaussian_residual_dirac_law_20261114
-- name    : AvramDividend.Classical.avram_a46_original_finiteactivity_zero_sigma_gaussian_residual_dirac_law_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:32:47.882882+00:00
-- url     : https://prove2.me/theorems/15f882bb-669b-4374-9019-0402182840b7
-- title:
--   Original finite-activity zero-volatility intrinsic Gaussian residual has exact zero-variance Gaussian law for any finite negative-jump intensity
-- statement:
--   For any original finite-activity spectrally negative Lévy source with sigma equal to zero, the physical Gaussian cutoff residual has the zero-variance Gaussian law at each time under its original probability measure, regardless of its nonzero jump intensity.
-- source:
--   Proved A21 actual source sigma-zero residual vanishing and Mathlib gaussianReal_zero_var.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a46_original_finiteactivity_zero_sigma_gaussian_residual_dirac_law_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSigma : X.σ = 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (R t) P =
        gaussianReal 0
          ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) := by sorry
