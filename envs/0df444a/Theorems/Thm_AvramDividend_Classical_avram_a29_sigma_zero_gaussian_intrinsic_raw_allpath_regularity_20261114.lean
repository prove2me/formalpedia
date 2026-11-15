-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
-- name    : AvramDividend.Classical.avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:05:47.617744+00:00
-- url     : https://prove2.me/theorems/e0706718-8bf2-4237-97e7-44220c53daf3
-- title:
--   Exact original raw-filtration all-path Gaussian intrinsic regularisation when sigma is zero
-- statement:
--   For an original finite-activity spectrally negative Levy source with zero Gaussian volatility, the intrinsic Gaussian limit admits a zero-start globally raw-adapted all-path cadlag no-positive-jump representative on exactly the original filtered probability space.
-- source:
--   Proved 594b2140 original zero-process Levy witness and Proved 77f47f2e source intrinsic Gaussian zero at sigma zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_zero_noise_original_filtered_levy_witness
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_sigma_zero_gaussian_residual_limit_ae_zero_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At zero Gaussian volatility the constant-zero original raw-adapted Levy witness regularises the intrinsic residual on all paths. -/

theorem AvramDividend.Classical.avram_a29_sigma_zero_gaussian_intrinsic_raw_allpath_regularity_20261114
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
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) := by sorry
