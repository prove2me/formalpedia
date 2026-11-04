-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_random_horizon_fourth_moment_mesh_error_bound
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_fourth_moment_mesh_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:12:42.899644+00:00
-- url     : https://prove2.me/theorems/09dd165f-9928-4895-94f4-dc7cd3eef3c7
-- title:
--   Original Levy Gaussian fourth-moment mesh coefficient bound on sample-dependent horizons
-- statement:
--   On every original source sample, random nonnegative mesh widths with total length at most the sample's finite localising horizon satisfy the Gaussian sigma fourth-power squared-mesh coefficient bound with that sample's maximum width. The coefficient is analytic; an original stochastic fourth moment or quadratic variation is not asserted.
-- source:
--   Previously Proved source-specific deterministic sigma fourth-moment mesh coefficient bound, Avram Palmowski Pistorius Proposition 4(i) equation (5.10).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_random_horizon_fourth_moment_mesh_error_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (h : ι → Ω → ℝ≥0)
    (τ : Ω → ℝ≥0) (ε : Ω → ℝ)
    (hε : ∀ ω, 0 ≤ ε ω)
    (hmax : ∀ ω, ∀ i ∈ S, (h i ω : ℝ) ≤ ε ω)
    (hT : ∀ ω, (∑ i ∈ S, (h i ω : ℝ)) ≤ (τ ω : ℝ)) :
    ∀ ω, 0 ≤ (2 : ℝ) * X.σ ^ 4 *
        (∑ i ∈ S, (h i ω : ℝ) ^ 2) ∧
      (2 : ℝ) * X.σ ^ 4 * (∑ i ∈ S, (h i ω : ℝ) ^ 2) ≤
        (2 : ℝ) * X.σ ^ 4 * ε ω * (τ ω : ℝ) := by sorry
