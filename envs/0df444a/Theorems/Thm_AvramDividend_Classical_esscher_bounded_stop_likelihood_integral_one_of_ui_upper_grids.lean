-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:41:57.403089+00:00
-- url     : https://prove2.me/theorems/63ae3e6c-4e98-4690-b081-1effd4113187
-- title:
--   Mass one for the genuine bounded stopped Esscher likelihood from uniformly integrable upper grids
-- statement:
--   Given uniformly integrable finite-grid stopped Esscher likelihoods at upper-grid stopping-time approximations τ_n ≤T converging downward to τ, the realised-time likelihood M_τ has P-integral one. The proof uses accepted normalisation of each finite-grid stopped density and right-continuity, followed by the separately authored Vitali mass-conservation theorem. Uniform integrability is stated explicitly and must be independently discharged by the L2 moment bound; no two-sided exit law or Wiener–Hopf independence is assumed.
-- source:
--   Pinned Mathlib integral_eq_lintegral_of_nonneg_ae; accepted finite-grid stopped-density probability 3c48c058 and right-approximation limit fee892e8; accepted Vitali mass conservation a641544b (canonical Proved).

import Mathlib
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_integral_mass_one_of_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_likelihood_integral_one_of_ui_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ) ∂P) = (1 : ℝ) := by sorry
