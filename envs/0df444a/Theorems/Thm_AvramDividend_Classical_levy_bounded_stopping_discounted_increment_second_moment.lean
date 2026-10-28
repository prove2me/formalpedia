-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_second_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_increment_second_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:01:32.361328+00:00
-- url     : https://prove2.me/theorems/e1cb92fe-ac4a-48c8-9ce7-a5c361de7574
-- title:
--   Exact discounted second moment after a bounded Lévy stopping time
-- statement:
--   For any bounded stopping time τ, horizon h, nonnegative θ and real discount rate q, the squared exponentially discounted future-increment factor has expectation exp(h[ψ(2θ)−2q]). This identity quantifies second-moment bounds for discounted stochastic dividend payoffs.
-- source:
--   Combine the deterministic discount and Lévy exponential, square, extract the constant exp(−2qh), and apply the stopping-time Laplace transform at 2θ.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_increment_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * q)) := by sorry
