-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:29:16.877954+00:00
-- url     : https://prove2.me/theorems/da14c844-4f72-4311-9d01-c59cdc960c24
-- title:
--   Original Levy Gaussian fourth moment quadratic variation mesh error quantitative bound
-- statement:
--   For the actual spectrally negative Levy process X, the canonical Gaussian variance σ² fixes the fourth-moment diagonal error coefficient 2σ⁴. On any nonnegative mesh of total length at most T and maximum width epsilon, its weighted sum of squared mesh widths is nonnegative and at most 2σ⁴ epsilon T. This is a quantitative algebraic component for Gaussian quadratic variation and proves both σ=0 and σ>0 branches without invoking auxiliary Brownian motion. Identification of actual stochastic error with this term requires upstream Gaussian independence and fourth moment proof.
-- source:
--   Quantitative mesh factor required for Gaussian quadratic variation in the original Levy Ito expansion, with variance coefficient defined by SpectrallyNegativeLevy. Proposition 4(i), equation (5.10) of Avram, Palmowski and Pistorius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (h : ι → ℝ≥0) (T ε : ℝ)
    (hε : 0 ≤ ε)
    (hmax : ∀ i ∈ S, (h i : ℝ) ≤ ε)
    (hT : (∑ i ∈ S, (h i : ℝ)) ≤ T) :
    0 ≤ (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) ∧
    (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) ≤
      (2 : ℝ) * X.σ ^ 4 * ε * T := by sorry
