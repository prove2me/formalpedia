-- Prove2me | Theorems.Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
-- name    : Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1914a8d8-176a-5391-b5a5-272a94f2ed70
-- title:
--   Holomorphic implicit function for a polynomial in one dependent variable
-- statement:
--   Let $n$ be a natural number and let $F$ be a polynomial in one variable with coefficients in the polynomial ring $\mathbb{C}[X_1,\dots,X_n]$ (Lean: `Polynomial (MvPolynomial (Fin n) ℂ)`), let $z_0 \in \mathbb{C}^n$ (a function $\mathrm{Fin}\,n \to \mathbb{C}$) and let $w_0 \in \mathbb{C}$. Assume that specialising the coefficients of $F$ at $z_0$ and then evaluating the resulting one-variable complex polynomial at $w_0$ gives $0$, and that the same procedure applied to the formal derivative $\mathrm{d}F/\mathrm{d}Y$ gives a nonzero value at $w_0$. The conclusion asserts the existence of real numbers $r,\rho$ and a function $\varphi \colon \mathbb{C}^n \to \mathbb{C}$ such that $r>0$, $\rho>0$, $\varphi(z_0)=w_0$, $\varphi$ is $\mathbb{C}$-differentiable on the metric ball $B(z_0,r)$ (for the product, i.e. sup, metric on $\mathbb{C}^n$) and moreover of class $\top$ over $\mathbb{C}$ there in Mathlib's smoothness scale (the top exponent), and two further properties: for every $z \in B(z_0,r)$ one has $\varphi(z) \in B(w_0,\rho)$ and $F$ with coefficients specialised at $z$ vanishes at $\varphi(z)$; and for every $z \in B(z_0,r)$ and every $w \in B(w_0,\rho)$, vanishing of $F$ specialised at $z$ at the point $w$ forces $w = \varphi(z)$.
--
--   This is the holomorphic implicit function theorem in the special case of a single polynomial equation $F(z,w)=0$ in $n$ base variables and one dependent variable, with a simple root in the $w$-direction; the implicit solution is obtained together with local existence, smoothness and local uniqueness on explicit product balls. It is used by [`Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential`](thm.html#Algebra.exists_bijOn_eval_differentiableOn_pi_of_smooth_of_kaehlerDifferential).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Topology Polynomial

theorem Complex.exists_differentiableOn_forall_eval_map_eval_eq_zero_iff_eq_of_derivative_ne_zero_pi
    {n : ℕ} (F : Polynomial (MvPolynomial (Fin n) ℂ)) (z₀ : Fin n → ℂ) (w₀ : ℂ)
    (h₀ : (F.map (MvPolynomial.eval z₀)).eval w₀ = 0)
    (hd : ((Polynomial.derivative F).map (MvPolynomial.eval z₀)).eval w₀ ≠ 0) :
    ∃ (r ρ : ℝ) (φ : (Fin n → ℂ) → ℂ), 0 < r ∧ 0 < ρ ∧ φ z₀ = w₀ ∧
      DifferentiableOn ℂ φ (Metric.ball z₀ r) ∧ ContDiffOn ℂ ⊤ φ (Metric.ball z₀ r) ∧
      (∀ z ∈ Metric.ball z₀ r, φ z ∈ Metric.ball w₀ ρ ∧ (F.map (MvPolynomial.eval z)).eval (φ z) = 0) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ w ∈ Metric.ball w₀ ρ, (F.map (MvPolynomial.eval z)).eval w = 0 → w = φ z) := by sorry
