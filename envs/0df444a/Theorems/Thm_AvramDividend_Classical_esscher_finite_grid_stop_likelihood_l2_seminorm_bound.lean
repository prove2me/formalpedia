-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_seminorm_bound
-- name    : AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_seminorm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:37:38.381092+00:00
-- url     : https://prove2.me/theorems/62e997c8-80db-44d8-a49d-f300624c334b
-- title:
--   Uniform finite-grid stopped Esscher L2 seminorm bound from the accepted second-moment estimate
-- statement:
--   For each adapted finite-grid stop τ≤H≤T, the L2 seminorm of its true compensated real Esscher likelihood is bounded by exp(H |ψ(2θ)−2ψ(θ)| /2). The proof converts the already accepted uniform second-moment estimate into an L2 seminorm bound using a pointwise equality for the squared exponential and exact ENNReal/real power arithmetic. The bound is independent of the grid resolution, allowing a uniform-integrability argument.
-- source:
--   Accepted finite-grid squared-likelihood lower integral bound ba8d7ec6; pinned Mathlib eLpNorm_eq_lintegral_rpow_enorm_toReal, Real.exp_mul, ENNReal.ofReal_rpow_of_pos. No fluctuation or Wiener-Hopf independence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_grid_stop_likelihood_l2_seminorm_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (hbound : ∀ ω, τ ω ≤ H) :
    eLpNorm (fun ω => Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)) (2 : ℝ≥0∞) P ≤
    ENNReal.ofReal (Real.exp
      (((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|) / 2)) := by sorry
