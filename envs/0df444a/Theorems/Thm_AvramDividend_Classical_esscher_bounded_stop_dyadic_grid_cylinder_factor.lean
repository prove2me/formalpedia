-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_dyadic_grid_cylinder_factor
-- name    : AvramDividend.Classical.esscher_bounded_stop_dyadic_grid_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T22:03:26.821996+00:00
-- url     : https://prove2.me/theorems/427d089b-34c3-4bda-a090-1ccaf8c79367
-- title:
--   Every bounded stopping-time dyadic approximation obeys one finite-terminal Esscher increment law
-- statement:
--   For a bounded genuine stopping time τ≤H, any stopped-history event A, tilt θ≥0 and finite Esscher terminal T≥H+1+u, every dyadic upper-rounded approximation τ_n satisfies Q_T(A and increment X_(τ_n+u)-X_(τ_n) in B)=Q_T(A) Q_u(X_u in B) for any Borel B. This is uniform in n and uses the full explicit bounded grid construction, with no full tilted strong Markov hypothesis.
-- source:
--   Proved bounded_stop_explicit_grid_increment_limit_with_horizon 062ac6d1, esscher_finite_grid_stop_future_increment_cylinder_factor c9bfc6f5, stoppedEvent_upperGridFibre_measurable ddc5c663 and stoppedHistory_event_measurable. Finite-terminal Esscher law of Kuznetsov–Kyprianou–Rivero.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_bounded_stop_explicit_grid_increment_limit_with_horizon
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_future_increment_cylinder_factor
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_dyadic_grid_cylinder_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ (n : ℕ) (B : Set ℝ), MeasurableSet B →
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
          (2 : ℝ≥0) ^ n + u) ω -
        X.X ((Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
          (2 : ℝ≥0) ^ n) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
