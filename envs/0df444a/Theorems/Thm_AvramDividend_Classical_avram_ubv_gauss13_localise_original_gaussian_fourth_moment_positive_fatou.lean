-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:51:40.867212+00:00
-- url     : https://prove2.me/theorems/46e23cf2-66bb-4572-9ae9-3ca9d70bb32f
-- title:
--   Original Gaussian fourth moment Fatou transfer from positive tilted law identities
-- statement:
--   For the original zero-jump spectrally negative Levy process and its measurable centred normalized actual fixed-time increment, the unweighted nonnegative fourth moment is bounded by the liminf of Gaussian-real reference fourth exponentially weighted moments at strictly positive parameters 1/(n+1). This is the exact original-side Fatou step needed before proving quantitative fourth-moment control for large-increment compact stopped Taylor L1 convergence. Gaussian-side continuity and the proportional-to-h² increment bound remain separately required. No negative-parameter MGF or surrogate Brownian path assumption.
-- source:
--   Proved e176b52c positive tilted original Gaussian fourth moments, Proved a42b9169 positive original exponential integrability, pinned Mathlib integrable_pow_mul_exp_of_mem_interior_integrableExpSet and lintegral_liminf_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss_top14_original_positive_theta_fourth_weighted_moment_eq_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_normalised_exponential_integrable

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_gaussian_fourth_moment_positive_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) (t : ℝ≥0)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X t ω - (t : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X t ω - (t : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    Filter.liminf (fun n : ℕ => ENNReal.ofReal
      (∫ z : ℝ, z ^ 4 * Real.exp ((1 / ((n : ℝ) + 1)) * z)
        ∂(gaussianReal 0 t))) atTop := by sorry
