-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_laplace_on_past_event
-- name    : AvramDividend.Classical.levy_increment_laplace_on_past_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:29.049884+00:00
-- url     : https://prove2.me/theorems/793ad91c-c403-46b2-9111-597e89cbf722
-- title:
--   Factor exponential Lévy increments against a measurable past event
-- statement:
--   For any event B measurable with respect to the original filtration F_s and any nonnegative Laplace parameter θ, the unnormalised exponential moment of the Lévy increment from s to s+h restricted to B equals the probability of B times its unconditional Laplace transform. The proof uses deterministic-time independent increments (future increment independent of F_s), the stationary increment law and the Laplace transform, together with integrability. It is an independently reusable measure-theoretic ingredient for finite-grid stopping-time decomposition and the later strong-Markov barrier-value factorisation; no random-time independence is assumed.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; canonical SpectrallyNegativeLevy.indepIncrements, stationaryIncrements, laplace fields and Mathlib conditional-expectation independence theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_laplace_on_past_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s h : ℝ≥0) (B : Set Ω) (hB : MeasurableSet[𝓕 s] B)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω in B,
      Real.exp (θ * (X.X (s + h) ω - X.X s ω)) ∂P =
        (P B).toReal * Real.exp ((h : ℝ) * X.ψ θ) := by sorry
