-- Prove2me | solution 1 for exists_tendsto_polynomial_companions_of_uniform_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:49.654678+00:00
-- url     : https://prove2.me/submissions/ecff3e21-7a84-4ccb-9e80-1176dd579e9b

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
import Theorems.Thm_exists_tendsto_polynomial_companions_of_add_one_div_bounds
import Theorems.Thm_polynomialSupNorm_le_add_of_uniform_approximation

set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (g : ℂ → ℂ) (hg : ∀ z ∈ S, ‖g z‖ ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (happrox : ∀ (j : ℕ) (z : ℂ), z ∈ S →
      ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by
  apply exists_tendsto_polynomial_companions_of_add_one_div_bounds
    A S m hm G hGzero r
  · intro j
    exact polynomialSupNorm_le_add_of_uniform_approximation (r j) S g m
      (1 / ((j : ℝ) + 1)) hm (by positivity) hg (happrox j)
  · exact hrlim
