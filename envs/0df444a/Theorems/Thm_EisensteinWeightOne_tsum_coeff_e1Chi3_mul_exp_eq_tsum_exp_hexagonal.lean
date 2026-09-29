-- Prove2me | Theorems.Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal
-- name    : EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/80f53ecd-83b7-563a-942a-5fe7babef5a0
-- title:
--   Hexagonal theta series equals the weight-one series E₁(χ₋₃)
-- statement:
--   Let $\sigma$ be a complex number with $\operatorname{Im}\sigma>0$. The assertion is the identity of (unconditional) infinite sums
--   $$\sum_{n\ge 0} c_n\, e^{2\pi i n\sigma}\;=\;\sum_{(a,b)\in\mathbb{Z}^2} e^{2\pi i \sigma (a^2+ab+b^2)},$$
--   where the left-hand side runs over natural numbers $n$ and $c_n\in\mathbb{Z}$, mapped into $\mathbb{C}$, is the $n$-th coefficient of the integral power series [`EisensteinWeightOne.e1Chi3`](def/ModularForm_EisensteinChiNegThree.html#L13), namely $c_0=1$ and $c_n=6\,\sigma_\chi(n)$ for $n\ge 1$ with $\sigma_\chi(n)=\sum_{d\mid n}$ `chiNegThree`$(d)$ the divisor sum of the integer-valued arithmetic function `chiNegThree`; the right-hand side runs over all pairs of integers $(a,b)$, the exponent being $2\pi i\sigma$ times the value $a^2+ab+b^2$ of the hexagonal quadratic form. Both sides are sums in the sense that assigns the value $0$ to a non-summable family, so the statement includes in particular the agreement of the two (absolutely convergent) series at every point of the upper half-plane.
--
--   This is the classical identity $\#\{(a,b)\in\mathbb{Z}^2: a^2+ab+b^2=n\}=6\sum_{d\mid n}\chi_{-3}(d)$ for $n\ge 1$, in the form of an equality of the theta series of the norm form of the Eisenstein integers with the $q$-expansion of the weight-one Eisenstein series attached to the character of conductor $3$. It is used in establishing that a suitable weight-one form has integral $q$-expansion coefficients in the relevant ring, via [`ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three`](thm.html#ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_le_two_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean

import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal (σ : ℂ) (hσ : 0 < σ.im) :
    (∑' n : ℕ, ((PowerSeries.coeff n EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * σ)) =
      ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by sorry
