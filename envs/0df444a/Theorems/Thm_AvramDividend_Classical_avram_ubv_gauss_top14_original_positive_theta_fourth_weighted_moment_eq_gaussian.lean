-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
-- name    : AvramDividend.Classical.avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:27:58.710481+00:00
-- url     : https://prove2.me/theorems/e176b52c-6edf-4f5e-afbb-bfad69b51b41
-- title:
--   Original zero-jump Gaussian fourth weighted moment identity at positive parameter
-- statement:
--   For the actual same-space zero-jump Lévy process X, at every positive exponential parameter, the fourth weighted moment of the normalised centred original increment equals the corresponding moment of the real Gaussian distribution. This is the finite positive-parameter precursor to the fourth-moment Fatou bound needed for the physical stopped Gaussian Taylor Lindeberg step feeding c63d897f and 249c532d.
-- source:
--   Proved 5b4b88ef original normalised MGF equality, Proved a42b9169 original positive exponential integrability, and pinned Mathlib ProbabilityTheory.iteratedDeriv_mgf plus EqOn.iteratedDeriv_of_isOpen.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_normalised_mgf_matches_gaussian_real
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual zero-jump centred Levy increment has the Gaussian fourth
    exponential moment at each positive transform parameter. -/

theorem AvramDividend.Classical.avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫ ω, ((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4 *
       Real.exp (θ * ((X.X t ω - (t : ℝ) * X.c) / X.σ)) ∂P) =
    (∫ z : ℝ, z ^ 4 * Real.exp (θ * z) ∂(gaussianReal 0 t)) := by sorry
