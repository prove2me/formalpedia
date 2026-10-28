-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stopped_density_probability
-- name    : AvramDividend.Classical.esscher_finite_grid_stopped_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:53:59.602879+00:00
-- url     : https://prove2.me/theorems/3c48c058-db76-437a-8d38-23370bbaa172
-- title:
--   Compensated Esscher exponential sampled on a finite stopping grid defines a probability law
-- statement:
--   At any adapted finite-valued stopping time τ whose possible values lie before a finite deterministic terminal T, the compensated exponential likelihood M_τ=exp(θ X_τ−τ ψ(θ)) has total P-mass one, so P.withDensity M_τ is a genuine probability measure. This is a finite-grid optional-sampling result proved from the accepted stopped-history likelihood equality and finite-terminal Esscher normalisation, without assuming optional stopping, an all-horizon tilted law or Wiener–Hopf independence.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2012), exponential change of measure equation (16) and martingale identity; accepted stopped-history likelihood equality 0c4f14ef-8514-41aa-a124-690734760e85 and accepted terminal Esscher normalisation chat04_esscher_weighted_finite_horizon_probability.

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_history
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_finite_grid_stopped_density_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ ω, τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s}) :
    IsProbabilityMeasure (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)))) := by sorry
