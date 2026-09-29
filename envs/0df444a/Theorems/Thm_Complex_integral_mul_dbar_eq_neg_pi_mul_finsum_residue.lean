-- Prove2me | Theorems.Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue
-- name    : Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e171e8c0-3659-5d83-ae7f-7bfa966b00c7
-- title:
--   Cauchy–Pompeiu formula for simple poles
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open and let $F,c:\mathbb{C}\to\mathbb{C}$ be functions with the following local property: for every $a\in U$ there is a function $g:\mathbb{C}\to\mathbb{C}$, analytic at $a$, such that $F(z)=c(a)/(z-a)+g(z)$ for all $z$ in some punctured neighbourhood of $a$ (i.e. eventually in the filter $\mathcal{N}[\neq]a$). Thus on $U$ the function $F$ agrees, off a discrete set, with a meromorphic function having at most simple poles, and $c(a)$ is its residue at $a$. Let $h:\mathbb{C}\to\mathbb{C}$ be continuously differentiable as a map of real vector spaces ($C^1$ in the sense of `ContDiff ℝ 1`), with compact support, and assume its topological support `tsupport h` is contained in $U$. Then the integral over $\mathbb{C}$, with respect to planar Lebesgue measure, of $F(z)\cdot\tfrac12\bigl(Dh(z)(1)+i\,Dh(z)(i)\bigr)$, where $Dh(z)$ is the real Fréchet derivative of $h$ at $z$, equals $-\pi\sum^{\mathrm f}_{a} c(a)\,h(a)$, the unrestricted `finsum` over $a\in\mathbb{C}$ of $c(a)h(a)$. The integrand's second factor is $\partial h/\partial\bar z$ in the usual notation.
--
--   This is the Cauchy–Pompeiu (generalised Cauchy) formula in the form $\iint F\,\partial_{\bar z}h\,dA=-\pi\sum_a\operatorname{Res}(F,a)h(a)$ for a function with at most simple poles tested against a compactly supported $C^1$ function; it is obtained by combining the vanishing of $\iint G\,\partial_{\bar z}h\,dA$ for $G$ holomorphic on a neighbourhood of $\operatorname{supp}h$ with the evaluation $\iint (z-a)^{-1}\partial_{\bar z}h\,dA=-\pi h(a)$. It is applied to logarithmic derivatives and, in that form, to the residue identity for level one used in the theory of modular forms on the upper half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory
open scoped Topology Real

theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a := by sorry
