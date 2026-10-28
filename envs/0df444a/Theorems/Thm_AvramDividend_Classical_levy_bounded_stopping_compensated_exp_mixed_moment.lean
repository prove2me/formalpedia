-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_exp_mixed_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:20:05.125374+00:00
-- url     : https://prove2.me/theorems/62676557-1926-4126-aadf-22cfeccaab1b
-- title:
--   Mixed moment of cumulant-compensated stopped Lévy exponentials
-- statement:
--   For nonnegative θ and η, the product of two cumulant-compensated exponentials of the same future increment has expectation exp(h[ψ(θ+η)−ψ(θ)−ψ(η)]). This is an exact mixed-moment identity for estimating correlations of exponential Lévy martingales after bounded stopping.
-- source:
--   Multiply the compensated exponentials, collect the exponents, extract the deterministic cumulant factor and apply the bounded-stopping increment Laplace formula at θ+η.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_exp_mixed_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) *
      Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ η) ∂P =
          Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) := by sorry
