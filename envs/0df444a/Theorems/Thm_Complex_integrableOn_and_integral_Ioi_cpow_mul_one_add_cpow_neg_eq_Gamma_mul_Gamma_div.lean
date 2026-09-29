-- Prove2me | Theorems.Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
-- name    : Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6db04a51-a79a-53b3-b7c6-deb5c621cff6
-- title:
--   Half-line Euler beta integral equals Γ(a)Γ(b)/Γ(a+b)
-- statement:
--   Let $a,b$ be complex numbers with $\operatorname{Re} a>0$ and $\operatorname{Re} b>0$. Consider the function of a real variable $v$ given by $v\mapsto v^{\,a-1}(1+v)^{-(a+b)}$, where both powers are complex powers (`Complex.cpow`) of the complex numbers obtained by coercing the reals $v$ and $1+v$. The assertion is a conjunction of two statements about this function on the open half-line $(0,\infty)$ with Lebesgue measure. First, it is integrable on $\mathrm{Ioi}\,0$, i.e. measurable there and of finite integral norm; note that the $\mathbb{C}$-valued Bochner integral used in the second part is therefore not the zero default value. Second, its integral over $(0,\infty)$ equals $\Gamma(a)\Gamma(b)/\Gamma(a+b)$, with $\Gamma$ the complex Gamma function of Mathlib and the quotient taken in $\mathbb{C}$ (under the hypotheses $\Gamma(a+b)\neq 0$, so the division is the genuine one).
--
--   This is Euler's beta integral in its half-line form, $B(a,b)=\int_0^\infty v^{a-1}(1+v)^{-(a+b)}\,dv$, packaged together with the absolute convergence needed to manipulate the integral. It is used in the computation of the Mellin transform of a product of archimedean Bessel kernels and in the attendant double-integral identities on $(0,\infty)^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integrableOn_and_integral_Ioi_cpow_mul_one_add_cpow_neg_eq_Gamma_mul_Gamma_div
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b))) (Set.Ioi 0) ∧
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ (a - 1) * (((1 + v : ℝ)) : ℂ) ^ (-(a + b)) =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by sorry
