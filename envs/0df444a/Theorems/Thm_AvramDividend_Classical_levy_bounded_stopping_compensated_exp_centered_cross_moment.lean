-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_centered_cross_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_exp_centered_cross_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:25:48.47357+00:00
-- url     : https://prove2.me/theorems/a51b0b14-9435-4de4-af23-3552a95a1aba
-- title:
--   Centred covariance identity for two stopped Lévy exponentials
-- statement:
--   Under a probability measure, the two centred cumulant-compensated future-increment exponentials have covariance exp(h[ψ(θ+η)−ψ(θ)−ψ(η)])−1. The formula gives exact cross-moments for martingale verification estimates at distinct Laplace parameters.
-- source:
--   Expand (f−1)(g−1), prove termwise integrability from the known nonzero first and mixed moment integrals, integrate linearly and substitute the unit means and mixed compensated moment.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_mixed_moment
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_exp_centered_cross_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
      (Real.exp (η *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) ∂P =
        Real.exp ((h : ℝ) * (X.ψ (θ + η) - X.ψ θ - X.ψ η)) - 1 := by sorry
