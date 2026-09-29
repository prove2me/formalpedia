-- Prove2me | Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul
-- name    : Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/60fc64df-100f-5097-a494-241ea69cc739
-- title:
--   One-pole Cauchy–Pompeiu formula for C¹ test functions
-- statement:
--   Let $a$ be a complex number and let $h \colon \mathbb{C} \to \mathbb{C}$ be continuously differentiable as a map between real normed spaces (`ContDiff ℝ 1 h`) and have compact support. Then the Bochner integral over $\mathbb{C}$, with respect to Lebesgue measure on the plane, of the function $$z \mapsto (z-a)^{-1} \cdot \tfrac{1}{2}\bigl(D_{\mathbb{R}}h(z)[1] + i\,D_{\mathbb{R}}h(z)[i]\bigr)$$ equals $-\pi\, h(a)$. Here $D_{\mathbb{R}}h(z)$ is the real Fréchet derivative of $h$ at $z$, so that $D_{\mathbb{R}}h(z)[1]$ and $D_{\mathbb{R}}h(z)[i]$ are the partial derivatives $\partial h/\partial x$ and $\partial h/\partial y$ at $z$, and the second factor is the Cauchy–Riemann combination $\partial h/\partial\bar z = \tfrac12(\partial_x h + i\,\partial_y h)$. The inverse $(z-a)^{-1}$ is understood with Lean's convention, taking the value $0$ at $z = a$, which affects a null set only; the kernel $1/|z-a|$ is locally integrable in the plane, so the integrand is indeed integrable and the asserted value is the genuine integral rather than the default value $0$. The constant $\pi$ is the real number $\pi$, coerced to $\mathbb{C}$.
--
--   This is the one-pole case of the Cauchy–Pompeiu formula, equivalently the statement that $1/(\pi z)$ is a fundamental solution of the Cauchy–Riemann operator $\partial/\partial\bar z$ on the plane. It is the local input for the $\bar\partial$-computations with logarithmic derivatives, being used by [`Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue`](thm.html#Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue) and by [`Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv`](thm.html#Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv), and it complements [`Complex.integral_mul_dbar_eq_zero_of_differentiableOn`](thm.html#Complex.integral_mul_dbar_eq_zero_of_differentiableOn), which gives the vanishing of such an integral when the kernel is holomorphic on a neighbourhood of the support of $h$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory
open scoped Real

theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a := by sorry
