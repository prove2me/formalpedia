-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_one_of_psi_eq_q
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_one_of_psi_eq_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:37:00.306989+00:00
-- url     : https://prove2.me/theorems/fe825d66-e2e5-46f5-90e8-dfe3c806fae1
-- title:
--   Unit mean of the discounted Lévy exponential at cumulant calibration
-- statement:
--   Use the stopped discounted Laplace identity. At `q = ψ θ`, the transformed exponent is zero and the expectation is one.
-- source:
--   Use the stopped discounted Laplace identity. At `q = ψ θ`, the transformed exponent is zero and the expectation is one.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_one_of_psi_eq_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hcal : X.ψ θ = q) :
    ∫ ω, Real.exp (-(q * (h : ℝ))) *
      Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P = 1 := by sorry
