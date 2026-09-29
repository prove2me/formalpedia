-- Prove2me | Theorems.Thm_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
-- name    : Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/7941a1cd-fadc-507f-85ab-791f8993899e
-- title:
--   Stokes form of the argument principle for E F'/F
-- statement:
--   Let $U\subseteq\mathbb C$ be an open set, let $F:\mathbb C\to\mathbb C$ be a function that is meromorphic at every point of $U$ and whose meromorphic order at each point of $U$ is different from $\top$ (so $F$ does not vanish identically near any point of $U$), let $E:\mathbb C\to\mathbb C$ be differentiable on $U$ in the complex sense, and let $h:\mathbb C\to\mathbb C$ be continuously differentiable as a function of the two real variables, with compact support and with $\operatorname{tsupport} h\subseteq U$. Then the integral over $\mathbb C$, with respect to planar Lebesgue measure, of $$E(z)\,\frac{F'(z)}{F(z)}\cdot\frac{\partial_1 h(z)+i\,\partial_I h(z)}{2}$$ — the second factor being $\partial h/\partial\bar z$, written with the real Fréchet derivative of $h$ at $z$ evaluated at the directions $1$ and $i$ — equals $-\pi$ times the finite sum, over $a\in\mathbb C$, of $\operatorname{ord}_a(F)\,E(a)\,h(a)$, where $\operatorname{ord}_a(F)$ is the integer obtained from `meromorphicOrderAt F a` by sending $\top$ to $0$, viewed in $\mathbb C$. Here $\operatorname{deriv}$, $E$ and $h$ are taken as given on all of $\mathbb C$, and the summand vanishes outside the zeros and poles of $F$ lying in the support of $h$.
--
--   This is the argument principle in Stokes (distributional) form: it expresses the identity $\partial_{\bar z}(F'/F)=\pi\sum_a\operatorname{ord}_a(F)\,\delta_a$, tested against a compactly supported $C^1$ function $h$ and weighted by a holomorphic factor $E$. It serves as the logarithmic-residue input for the smoothed treatment of differentials of the third kind on modular curves, and is used in the two statements [`ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_exp) and [`ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Complex
open scoped Topology Real

theorem Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a := by sorry
