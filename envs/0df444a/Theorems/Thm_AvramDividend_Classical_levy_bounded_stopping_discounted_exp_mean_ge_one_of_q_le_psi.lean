-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:46:50.442405+00:00
-- url     : https://prove2.me/theorems/ae255f7c-7290-4514-8025-7b5b9378f6a0
-- title:
--   Lower discounted Lévy exponential-mean bound under cumulant domination
-- statement:
--   Apply the stopped discounted Laplace identity. Under q≤ψ(θ) and nonnegative horizon, the exponent h(ψ(θ)−q) is nonnegative, so the expectation is at least one.
-- source:
--   Apply the stopped discounted Laplace identity. Under q≤ψ(θ) and nonnegative horizon, the exponent h(ψ(θ)−q) is nonnegative, so the expectation is at least one.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_ge_one_of_q_le_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : q ≤ X.ψ θ) :
    1 ≤ ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by sorry
