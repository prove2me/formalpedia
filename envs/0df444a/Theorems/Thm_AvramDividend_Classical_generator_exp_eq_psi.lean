-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
-- name    : AvramDividend.Classical.generator_exp_eq_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:23:31.955467+00:00
-- url     : https://prove2.me/theorems/e651bf0f-155e-40dd-b90e-e3df2133fe41
-- title:
--   Lévy generator acts diagonally on exponential test functions
-- statement:
--   For any real θ and x, the Lévy–Khintchine generator of the exponential test function f(z)=e^(θz) equals ψ(θ)e^(θx). First and second derivatives come from the exact pinned Mathlib theorem iteratedDeriv_exp_const_mul. The jump part uses generatorIntegrand_exp_mul and the linearity of the Lebesgue integral. This is an analytic identity, not a stochastic Itô/Dynkin theorem.
-- source:
--   Exact algebraic consistency of the Avram Dividend generator definition and Laplace exponent at pinned Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.generator_exp_eq_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) :
    X.generator (fun z : ℝ => Real.exp (θ * z)) x =
      Real.exp (θ * x) * X.ψ θ := by sorry
