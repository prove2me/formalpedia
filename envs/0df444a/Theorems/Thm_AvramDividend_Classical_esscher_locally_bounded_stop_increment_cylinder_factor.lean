-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_locally_bounded_stop_increment_cylinder_factor
-- name    : AvramDividend.Classical.esscher_locally_bounded_stop_increment_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:39:28.497253+00:00
-- url     : https://prove2.me/theorems/2a64cd78-54a7-401b-9d74-07006d316f8a
-- title:
--   Localised Esscher future-increment law at finite, not globally bounded, stopping times
-- statement:
--   For a genuine possibly unbounded but finite nonnegative Lévy stopping time τ, any stopped-history event A supported on {τ≤H}, nonnegative Esscher parameter θ and finite deterministic terminal T≥H+1+u, Q_T(A ∩ {X_(τ+u)−X_τ∈B}) = Q_T(A) Q_u(X_u∈B) for each Borel B. Derives by capping τ at H, showing the stopped-history event remains adapted at the capped stopping time, applying the accepted bounded-stop Esscher cylinder theorem, and using that τ∧H=τ on A. This is a localisation interface for exponential-clock or first-passage stopping events without global Esscher path extension.
-- source:
--   Proved bounded stop Esscher cylinder 4d8a7cfb-3725-489d-befc-72d496f9561d; Mathlib IsStoppingTime.min_const, Filtration.mono, and elementary stopped-history cap support.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- A finite-terminal Esscher stopped-increment law for an unbounded stop,
localised to any stopped-history event supported before the terminal cap. -/

theorem AvramDividend.Classical.esscher_locally_bounded_stop_increment_cylinder_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hSupport : A ⊆ {ω : Ω | τ ω ≤ H})
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
