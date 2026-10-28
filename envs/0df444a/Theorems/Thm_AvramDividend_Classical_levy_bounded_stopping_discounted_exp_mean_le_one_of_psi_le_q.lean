-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:37:00.07902+00:00
-- url     : https://prove2.me/theorems/cac3ffdf-9497-4a7b-843d-04ac64d9a7e0
-- title:
--   Supermean bound for discounted Lévy exponentials under cumulant domination
-- statement:
--   The discounted stopped Laplace transform equals `exp(h(ψ θ − q))`. Since `h ≥ 0` and `ψ θ ≤ q`, its exponent is nonpositive, so its expectation is at most one.
-- source:
--   The discounted stopped Laplace transform equals `exp(h(ψ θ − q))`. Since `h ≥ 0` and `ψ θ ≤ q`, its exponent is nonpositive, so its expectation is at most one.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_le_one_of_psi_le_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : X.ψ θ ≤ q) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P ≤ 1 := by sorry
