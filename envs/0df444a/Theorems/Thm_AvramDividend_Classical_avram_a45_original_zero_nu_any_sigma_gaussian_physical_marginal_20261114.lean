-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
-- name    : AvramDividend.Classical.avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:31:42.314028+00:00
-- url     : https://prove2.me/theorems/d2d064d5-fd25-4bce-91d7-6430ceeffafe
-- title:
--   Any zero-jump original intrinsic Gaussian residual has exact centred Gaussian marginal law at every volatility
-- statement:
--   For every original finite-activity zero-jump Lévy source including zero volatility, its intrinsic physical Gaussian residual has exact centred Gaussian marginal with variance sigma squared times time under its original measure.
-- source:
--   Proved A21 degenerate sigma-zero source theorem and A44 positive-sigma physical Gaussian law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a45_original_zero_nu_any_sigma_gaussian_physical_marginal_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hNu : X.ν = 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ t : ℝ≥0,
      Measure.map (R t) P =
        gaussianReal 0
          ((NNReal.mk (X.σ ^ 2) (sq_nonneg X.σ)) * t) := by sorry
