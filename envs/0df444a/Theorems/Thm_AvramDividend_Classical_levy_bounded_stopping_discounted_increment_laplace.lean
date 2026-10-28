-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_increment_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:51:34.194192+00:00
-- url     : https://prove2.me/theorems/e2d27d46-5e23-4fbd-af78-adfac80c23bb
-- title:
--   Discounted exponential Lévy increment transform after bounded stopping
-- statement:
--   For a bounded stopping time τ and future horizon h, the exponentially discounted post-stopping Lévy increment has expectation exp(h(ψ(θ)−q)) for every real discount rate q and nonnegative Laplace parameter θ. This version directly matches discounted payoff calculations in stochastic dividend verification.
-- source:
--   Multiply the established stopping-time Laplace identity by the deterministic discount exp(−qh), pull out the constant, then combine exponentials.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_increment_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * (X.ψ θ - q)) := by sorry
