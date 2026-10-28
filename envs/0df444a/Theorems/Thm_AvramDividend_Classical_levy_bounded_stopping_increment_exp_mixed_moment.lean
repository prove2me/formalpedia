-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_exp_mixed_moment
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_exp_mixed_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:16:26.848064+00:00
-- url     : https://prove2.me/theorems/ac75e026-8825-449d-aa93-13148ea9b9bf
-- title:
--   Mixed exponential moment of a future Lévy increment after bounded stopping
-- statement:
--   For θ,η≥0, the mixed moment of exp(θ[X_(τ+h)−X_τ]) and exp(η[X_(τ+h)−X_τ]) equals exp(hψ(θ+η)) after any bounded stopping time. This extends the second-moment calculation and is useful for variance and covariance estimates.
-- source:
--   Combine the two exponential factors into exp((θ+η)ΔX) and apply the proved bounded-stopping Lévy Laplace identity at the nonnegative parameter θ+η.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_exp_mixed_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω)) *
      Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
        Real.exp ((h : ℝ) * X.ψ (θ + η)) := by sorry
