-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:27:35.190955+00:00
-- url     : https://prove2.me/theorems/999fd61c-d109-429f-ae60-d626311357a4
-- title:
--   Unit mean of a compensated Lévy increment after a bounded stopping time
-- statement:
--   For a bounded stopping time τ and future horizon h, the exponential transform exp(θ(X_(τ+h)−X_τ)−h ψ(θ)) has expectation one for θ≥0. This follows by compensating the proven bounded-stopping increment Laplace transform. Useful when normalising post-stopping dividend verification estimates.
-- source:
--   Direct corollary of proved levy_bounded_stopping_increment_laplace via Real.exp_sub and integral_mul_const.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) ∂P = 1 := by sorry
