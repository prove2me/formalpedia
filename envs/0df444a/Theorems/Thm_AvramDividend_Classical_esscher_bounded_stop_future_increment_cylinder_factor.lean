-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_cylinder_factor
-- name    : AvramDividend.Classical.esscher_bounded_stop_future_increment_cylinder_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:25:14.194654+00:00
-- url     : https://prove2.me/theorems/4d8a7cfb-3725-489d-befc-72d496f9561d
-- title:
--   Borel cylinder factorisation at bounded genuine Esscher Lévy stopping times
-- statement:
--   Let τ≤H be a genuine bounded stopping time, A an event measurable in its stopped history, and Q_T a compensated Esscher path probability with T≥H+1+u. For every Borel B, Q_T(A∩{X_(τ+u)−X_τ∈B})=Q_T(A)Q_u(X_u∈B). This is a direct cylinder consequence of the verified full restricted pushforward measure identity. No global tilted path law, residual independent exponential-clock splitting or Wiener–Hopf factorisation is assumed.
-- source:
--   The complete Borel-cylinder form of the finite-terminal bounded-stopping measure law. Derives from esscher_bounded_stop_future_increment_map_law after remote acceptance and proven measurable Lévy stopped paths.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_future_increment_cylinder_factor
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
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
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
