-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_hjb_supersolution_positive
-- name    : AvramDividend.Classical.levy_exponential_hjb_supersolution_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:49:38.897007+00:00
-- url     : https://prove2.me/theorems/18391269-bd5f-49ef-bc97-747effb0b8ac
-- title:
--   Exponential Lévy test function satisfies both HJB supersolution inequalities on nonnegative reserves
-- statement:
--   For any spectrally negative Lévy process, real q, exponential parameter θ≥1 and starting reserve x≥0, if the Lévy Laplace exponent ψ(θ)≤q, then Γ(exp(θ·))(x)≤q exp(θx) and the spatial derivative of exp(θ·) at x is at least one. The generator bound uses the already Proved generator_exp_eq_psi and positivity of the exponential. The derivative bound uses the pinned iteratedDeriv_exp_const_mul identity, 1+θx≤exp(θx) and θ≥1. This verifies the two pointwise classical HJB inequalities for a concrete smooth positive test function, without asserting the missing stopped stochastic dividend verification theorem.
-- source:
--   Pinned generator_exp_eq_psi theorem and Real.add_one_le_exp/iteratedDeriv_exp_const_mul at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_hjb_supersolution_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q x : ℝ) (hθ : 1 ≤ θ) (hx : 0 ≤ x)
    (hψ : X.ψ θ ≤ q) :
    X.generator (fun z : ℝ => Real.exp (θ * z)) x ≤
        q * Real.exp (θ * x) ∧
      1 ≤ deriv (fun z : ℝ => Real.exp (θ * z)) x := by sorry
