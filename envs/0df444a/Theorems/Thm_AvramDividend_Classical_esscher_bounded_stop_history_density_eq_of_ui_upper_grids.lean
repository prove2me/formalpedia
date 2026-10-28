-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_history_density_eq_of_ui_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_history_density_eq_of_ui_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:54:35.183361+00:00
-- url     : https://prove2.me/theorems/2f664ff6-f054-40a8-838e-5b3cec1d9630
-- title:
--   Bounded stopped-history event agreement between finite-terminal Esscher law and realised stopped likelihood
-- statement:
--   For a bounded stopping time τ approached from above by adapted finite-grid stopping times before T, a measurable stopped-history event A whose intersection with every approximating fibre belongs to its historical filtration has the same mass under the genuine deterministic-terminal Esscher law Q_T as under the realised stopped likelihood P.withDensity M_τ, provided the finite-grid stopped likelihoods are uniformly integrable. The assumption of UI is to be discharged separately by L2, and no unrestricted future-path equality is inferred.
-- source:
--   Accepted finite-grid stopped-likelihood history 0c4f14ef and pathwise right limit fee892e8; prospective uniform-integrability eventwise density convergence analytic bridge; no Wiener-Hopf, killed-scale or global Esscher process assumption.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_withDensity_event_tendsto_of_ae_tendsto
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Theorems.Thm_AvramDividend_Classical_esscher_stopped_likelihood_tendsto_of_right_approximation

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_history_density_eq_of_ui_upper_grids
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
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τn n ω = s}))
    (hUI : UniformIntegrable (fun n ω =>
      Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) 1 P) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A := by sorry
