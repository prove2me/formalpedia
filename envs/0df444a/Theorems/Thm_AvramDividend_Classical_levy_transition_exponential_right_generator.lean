-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_right_generator
-- name    : AvramDividend.Classical.levy_transition_exponential_right_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:05:41.315195+00:00
-- url     : https://prove2.me/theorems/20c8d029-9683-446a-8871-06ae8e192a65
-- title:
--   Right-hand transition semigroup slope equals the Lévy generator on exponential test functions
-- statement:
--   Let X be the given spectrally negative Lévy process, θ≥0 and x a deterministic starting reserve. For positive real h tending down to zero, regard h as nonnegative time via Real.toNNReal and take the divided difference of the actual transition expectation E[exp(θ(x+X_h))] relative to exp(θx). Prove that the quotient tends to Γ(exp(θ·))(x). For positive h, Real.coe_toNNReal identifies the time argument; the Proved exponential transition eigenfunction gives exp(θx)exp(hψθ), the Proved analytic derivative implies the right slope through pinned HasDerivAt.tendsto_slope_zero_right, and the Proved generator_exp_eq_psi identifies the limit. This is an actual stochastic semigroup generator limit on the exponential test-function class, not the general C² generator identity or stopped stochastic dividend verification. This second publication version repairs the unresolved neighbourhood notation in the original specification, preserving the same mathematical proposition.
-- source:
--   Proved exact exponential transition identity, Proved exponential multiplier derivative and Γ-exp identity; pinned Mathlib HasDerivAt.tendsto_slope_zero_right and Real.coe_toNNReal. Original publication job aea4606a-39e0-4a44-b358-1438ba1cc109 failed formal-statement compilation because neighbourhood notation 𝓝 was unresolved; this version uses explicit Filter.nhdsWithin and Filter.nhds identifiers.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
import Theorems.Thm_AvramDividend_Classical_levy_exponential_semigroup_multiplier_deriv_zero
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_exponential_right_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) (hθ : 0 ≤ θ) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ * ((∫ ω, Real.exp (θ * (x + X.X (Real.toNNReal h) ω)) ∂P) -
          Real.exp (θ * x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z : ℝ => Real.exp (θ * z)) x)) := by sorry
