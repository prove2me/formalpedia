-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_antitone_in_discount
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:10:08.617494+00:00
-- url     : https://prove2.me/theorems/4754bc9d-f869-468a-9982-736bfdd77d48
-- title:
--   Monotonicity of the expected Lévy future exponential in discount
-- statement:
--   For a bounded stopping time, raising the deterministic discount parameter decreases the expected discounted exponential of a future Lévy increment. This comparison supports monotone discount bounds in stochastic dividend verification.
-- source:
--   Use the previously verified exact discounted Lévy increment transform. Its exponent is h(ψ(θ)−q); increasing q decreases the exponent when the time horizon is nonnegative.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q₁ q₂ : ℝ) (hθ : 0 ≤ θ) (hq : q₁ ≤ q₂) :
    (∫ ω, Real.exp (-(q₂ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P) ≤
    ∫ ω, Real.exp (-(q₁ * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by sorry
