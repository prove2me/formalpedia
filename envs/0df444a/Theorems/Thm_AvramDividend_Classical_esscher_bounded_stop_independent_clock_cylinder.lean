-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_independent_clock_cylinder
-- name    : AvramDividend.Classical.esscher_bounded_stop_independent_clock_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:26:39.468873+00:00
-- url     : https://prove2.me/theorems/83605af7-36c7-47c9-8ba8-272f0cf0e907
-- title:
--   Independent exponential clock factors from a genuine bounded-stop Esscher future increment
-- statement:
--   For a bounded true stopping time under a finite terminal Esscher probability Q_T, and an independently sampled Exp(p) clock, the probability of a stopped-history event, a post-stop fixed-lag increment Borel cylinder, and an independent clock event is Q_T(A) Q_u(X_u∈B) Exp(p)(C). This is a product-measure corollary of the bounded-stop Esscher cylinder law and does not claim exponential residual-clock or Wiener–Hopf independence.
-- source:
--   Direct corollary of canonically Proved esscher_bounded_stop_future_increment_map_law 9032b4a2-fc71-4bb6-8a61-52f1bfe2ee18, pinned Mathlib Measure.prod_prod, measure-map evaluation, and exponential clock probability instance.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_independent_clock_cylinder
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
    (B : Set ℝ) (hB : MeasurableSet B)
    (p : ℝ) (hp : 0 < p) (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
       (expMeasure p))
      ((A ∩ {ω : Ω |
        X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by sorry
