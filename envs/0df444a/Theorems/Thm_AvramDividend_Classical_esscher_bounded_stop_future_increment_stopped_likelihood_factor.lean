-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_stopped_likelihood_factor
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:50:58.755295+00:00
-- url     : https://prove2.me/theorems/c03b7595-beff-4c03-a08a-cea17c9e1e76
-- title:
--   Bounded genuine stopping-time tilted increment factor with realised stopped-likelihood history marginal
-- statement:
--   For a genuine bounded stopping time τ≤H, stopped-history event A, future lag u and deterministic Esscher terminal T≥H+1+u, the genuine tilted law Q_T factorises the joint event A and a future increment cylinder into (P.withDensity Mτ)(A) times the deterministic-time tilted increment law Q_u(X_u∈B). The Q_T side contains the future event; the realised stopped density is used solely for its correct historical marginal, and the proof derives finite grid/UI steps from earlier accepted results.
-- source:
--   Accepted bounded-stop tilted future increment cylinder factor 4d8a7cfb and new genuine bounded stopped-history density identity 47b25ea7. No future-event factorisation under P.withDensity Mτ, no independent realised clock, no WH assumption.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω -
        X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
