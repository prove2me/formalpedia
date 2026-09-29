-- Prove2me | Theorems.Thm_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
-- name    : Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9902931c-6f51-5807-98b5-b1bc1cd38b08
-- title:
--   Holomorphic implicit function theorem for a bivariate polynomial
-- statement:
--   Let $F$ be a polynomial in one variable over $\mathbb{C}[X]$, that is an element of $\mathbb{C}[X][Y]$, and let $z_0, w_0 \in \mathbb{C}$. Write $F.\mathrm{evalEval}\,z\,w$ for the value obtained by substituting $z$ for the inner variable and $w$ for the outer one, i.e. $F(z,w)$. Assume $F(z_0,w_0) = 0$ and that the derivative of $F$ with respect to the outer variable $Y$ does not vanish at $(z_0,w_0)$, i.e. $(\partial_Y F)(z_0,w_0) \neq 0$. The conclusion asserts the existence of real numbers $r, \rho$ and a function $\varphi : \mathbb{C} \to \mathbb{C}$ such that $r > 0$, $\rho > 0$, $\varphi(z_0) = w_0$, the function $\varphi$ is complex-differentiable on the open ball $B(z_0,r)$, for every $z \in B(z_0,r)$ one has $\varphi(z) \in B(w_0,\rho)$ together with $F(z,\varphi(z)) = 0$, and, for every $z \in B(z_0,r)$ and every $w \in B(w_0,\rho)$, the equation $F(z,w) = 0$ forces $w = \varphi(z)$. Thus $\varphi$ parametrises, holomorphically and uniquely, the zeros of $F$ in the bidisc $B(z_0,r) \times B(w_0,\rho)$. Note that $\varphi$ is a globally defined function on $\mathbb{C}$ whose properties are asserted only on $B(z_0,r)$.
--
--   This is the holomorphic implicit function theorem in the special case of a single polynomial equation $F(z,w)=0$ in two complex variables, with the non-degeneracy hypothesis $\partial_Y F \neq 0$ at the base point. It is used to produce local holomorphic sections, and thence complex-analytic charts, for smooth affine curves: it is cited by [`Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential`](thm.html#Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology Polynomial

theorem Complex.exists_differentiableOn_forall_evalEval_eq_zero_iff_eq_of_evalEval_derivative_ne_zero
    (F : Polynomial (Polynomial ℂ)) (z₀ w₀ : ℂ)
    (h₀ : F.evalEval z₀ w₀ = 0) (hd : (Polynomial.derivative F).evalEval z₀ w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : ℂ → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ F.evalEval z (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, F.evalEval z w = 0 → w = φ z) := by sorry
