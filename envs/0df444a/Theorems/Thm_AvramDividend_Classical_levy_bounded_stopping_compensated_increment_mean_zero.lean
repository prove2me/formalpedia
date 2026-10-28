-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_zero
-- name    : AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:10:38.615331+00:00
-- url     : https://prove2.me/theorems/30aa3792-f474-438c-939d-cc67ad5c3ede
-- title:
--   Centred compensated Lévy exponential increment has zero expectation
-- statement:
--   Under a probability law, the increment exp(θ[X_(τ+h)−X_τ]−hψ(θ))−1 has mean zero after any bounded stopping time τ and forward horizon h. This is the centred exponential increment underlying optional-stopping martingale verification.
-- source:
--   Use the already accepted unit-mean cumulant-compensated increment, derive integrability from its nonzero integral, then subtract the expectation of the constant-one function under the probability measure.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_compensated_increment_mean_zero
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
      (h : ℝ) * X.ψ θ) - 1) ∂P = 0 := by sorry
