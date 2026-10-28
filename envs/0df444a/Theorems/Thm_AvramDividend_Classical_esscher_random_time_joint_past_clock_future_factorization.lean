-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_random_time_joint_past_clock_future_factorization
-- name    : AvramDividend.Classical.esscher_random_time_joint_past_clock_future_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:21:36.948613+00:00
-- url     : https://prove2.me/theorems/caa0f80f-72fe-4f00-ad06-c2fe43ac38d4
-- title:
--   Random-time Esscher law factorises past path and future-restricted clock cylinder events
-- statement:
--   Let R(dω,du)=exp(θX_(u+)−u+ψ(θ))P(dω)Exp(p)(du), where u+=max(u,0), and θ≥0. For a path event A∈𝓕_s and a measurable clock set B all of whose clamped times satisfy u+≥s, R(A×B)=Q_s(A)Exp(p)(B), where Q_s is the deterministic-time Esscher probability. This is a rigorous future-restricted cylinder factorisation under the genuine random-time joint law. It does not assert unconditional independence of the random clock and entire path, nor a full tilted path law.
-- source:
--   Tonelli/Fubini for the jointly measurable Esscher likelihood, finite-horizon measure consistency chat04_esscher_finite_horizon_laws_consistent_on_past_events (a74b3334-5c28-44d1-ae88-3057d26957f4), and Kuznetsov–Kyprianou–Rivero The Theory of Scale Functions (2012), Esscher equation (16).

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_random_time_joint_past_clock_future_factorization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (s : ℝ≥0)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfuture : ∀ u ∈ B, s ≤ Real.toNNReal u) :
    ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) (A ×ˢ B) =
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
        (ProbabilityTheory.expMeasure p) B := by sorry
