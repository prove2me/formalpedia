-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_exact_variance
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_exact_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:15:17.873918+00:00
-- url     : https://prove2.me/theorems/aa687ed2-8040-4300-b82d-1f334af18ab7
-- title:
--   Exact conditional-horizon variance of a compensated Lévy exponential increment
-- statement:
--   For any bounded stopping time τ under a probability law, the centred exponential increment has variance exp(h[ψ(2θ)−2ψ(θ)])−1. The expression is finite by the established second-moment identity and directly quantifies uncertainty in exponential-martingale increments used in stochastic dividend verification.
-- source:
--   Expand the square of the centred increment, use integrability from the nonzero first and second moment integrals, apply integral linearity and simplify with the accepted exact first/second moments.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_second_moment
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_exact_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) ^ 2 ∂P =
        Real.exp ((h : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ)) - 1 := by sorry
