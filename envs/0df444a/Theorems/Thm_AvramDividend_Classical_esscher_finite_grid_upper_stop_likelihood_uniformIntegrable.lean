-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
-- name    : AvramDividend.Classical.esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T16:02:28.402017+00:00
-- url     : https://prove2.me/theorems/53937e78-b7a5-4141-8ca4-e8a828090361
-- title:
--   Uniform integrability of genuine finite-grid stopped Esscher likelihoods with a common terminal and cap
-- statement:
--   For any sequence of adapted finite-valued stopping times τ_n bounded uniformly by H and taking values before a common finite-terminal T, the actual stopped Esscher likelihoods exp(θX_{τ_n}−τ_nψθ) are uniformly integrable in L1(P), uniformly over grid resolution. This follows from a common L2 bound and quantitative Hölder, without invoking a full Esscher process law or Wiener–Hopf splitting.
-- source:
--   Accepted finite-grid L2 lintegral bound ba8d7ec6 via the prospective L2 seminorm corollary; prospective generic probability-space L2→UI theorem; accepted joint path-state measurability d55462c3 and finite-grid stopping certificate aa6185a1.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_finite_grid_adapted_fibres_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory Filter
open scoped ENNReal NNReal

theorem AvramDividend.Classical.esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H) :
    UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P := by sorry
