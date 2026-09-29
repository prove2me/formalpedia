-- Prove2me | Theorems.Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn
-- name    : Complex.integral_mul_dbar_eq_zero_of_differentiableOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/535b105b-db00-5179-bc38-7bd7f1baae6b
-- title:
--   Holomorphic functions are weak solutions of partial̄
-- statement:
--   Let $V \subseteq \mathbb{C}$ be an open set, let $G \colon \mathbb{C} \to \mathbb{C}$ be a function that is complex-differentiable at every point of $V$ in the sense of `DifferentiableOn ℂ G V` (no hypothesis is placed on $G$ outside $V$), and let $h \colon \mathbb{C} \to \mathbb{C}$ be continuously differentiable as a map of real normed spaces (`ContDiff ℝ 1 h`), with compact support, whose topological support $\operatorname{tsupport} h$ is contained in $V$. Then the Bochner integral over $\mathbb{C}$, with respect to the ambient (Lebesgue) measure on $\mathbb{C}$, of
--   $$z \mapsto G(z)\,\frac{(D h)_z(1) + i\,(D h)_z(i)}{2}$$
--   vanishes, where $(Dh)_z$ denotes the real Fréchet derivative `fderiv ℝ h z` of $h$ at $z$, so that $(Dh)_z(1)$ and $(Dh)_z(i)$ are the partial derivatives $\partial h/\partial x$ and $\partial h/\partial y$ at $z$ and the second factor is $(\partial h/\partial\bar z)(z)$. Thus $\int_{\mathbb{C}} G\,\partial_{\bar z}h\, dA = 0$ for every test function $h$ of class $C^1$ with compact support inside $V$.
--
--   This is Cauchy's theorem in distributional (Stokes) form: a function holomorphic on $V$ is a weak solution of the Cauchy–Riemann operator $\partial/\partial\bar z$ on $V$. It is the pole-free case underlying the Cauchy–Pompeiu formula, and is used by [`Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul`](thm.html#Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul) and [`Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue`](thm.html#Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue), which in turn feed the Stokes-type computation of Petersson pairings on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory

theorem Complex.integral_mul_dbar_eq_zero_of_differentiableOn
    (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 := by sorry
