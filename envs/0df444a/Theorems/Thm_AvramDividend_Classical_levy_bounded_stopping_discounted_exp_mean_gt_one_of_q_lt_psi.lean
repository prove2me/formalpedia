-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:53:15.468996+00:00
-- url     : https://prove2.me/theorems/f9d09313-1fbc-498c-9ae2-c01ba4f0cc8b
-- title:
--   Strict lower bound for discounted Lévy exponential expectation
-- statement:
--   For strictly positive horizon and q<ψ(θ), the stopped discounted exponential transform has strictly positive exponent h(ψ(θ)−q), hence its expected value exceeds one.
-- source:
--   For strictly positive horizon and q<ψ(θ), the stopped discounted exponential transform has strictly positive exponent h(ψ(θ)−q), hence its expected value exceeds one.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_gt_one_of_q_lt_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (hh : 0 < h) (θ q : ℝ) (hθ : 0 ≤ θ)
    (hlt : q < X.ψ θ) :
    1 < ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P := by sorry
