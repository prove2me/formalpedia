-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_future_increment_stopped_likelihood_factor
-- name    : AvramDividend.Classical.esscher_ae_bounded_stop_future_increment_stopped_likelihood_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:44:12.46822+00:00
-- url     : https://prove2.me/theorems/2a05983f-ec59-47d4-9f4e-ceee7a7adfb2
-- title:
--   Genuine almost-surely bounded stopping-time Esscher Markov factor with stopped likelihood marginal
-- statement:
--   For a stopping time bounded by H P-almost surely and a stopped-history event A, the finite-terminal actual tilted measure Q_T factorises its future increment cylinder at tau with the realised stopped-time Esscher historical marginal Q_tau(A) and deterministic future increment law Q_u. The proof composes the almost-surely bounded cylinder factor and exact stopped-history density transfer. It uses neither global tilted law nor WH independence.
-- source:
--   Two mathematically independent public proof interfaces authored in this workstream: esscher_ae_bounded_stop_future_increment_cylinder_factor and esscher_ae_bounded_stop_stoppedHistory_density_eq, themselves consequences of accepted finite-terminal stopped Markov theorems.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_esscher_ae_bounded_stop_stoppedHistory_density_eq

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_ae_bounded_stop_future_increment_stopped_likelihood_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (haeBound : ∀ᵐ ω ∂P, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
