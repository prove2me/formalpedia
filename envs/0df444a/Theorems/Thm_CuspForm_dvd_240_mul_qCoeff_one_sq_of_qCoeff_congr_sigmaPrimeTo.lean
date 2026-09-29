-- Prove2me | Theorems.Thm_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c536d50f-c963-5dc0-a735-07e580ae6fcd
-- title:
--   Divisibility forced by an Eisenstein congruence on Γ₀(p)
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $m \ge 2$. Let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, and let $af : \mathbb{N} \to \mathbb{Z}$ be a sequence of integers which computes the $q$-expansion coefficients of $f$, in the sense that for every $n$ the complex number $af(n)$ equals the $n$-th coefficient of the $q$-expansion of $f$ of width $1$ (the coefficient extracted by [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19)). Assume the congruence hypothesis that for every $n \neq 0$ the integer $m$ divides $af(n) - \sigma'_p(n)\, af(1)$, where $\sigma'_p(n)$, written `sigmaPrimeTo p n`, is the sum of those divisors $d$ of $n$ with $p \nmid d$. The conclusion is a divisibility of integers: $24m$ divides
--   $$240\,af(1)^2\,(p-1)^2\,(p+1).$$
--
--   This is a constant-term forcing step in the style of Mazur's study of the Eisenstein ideal, carried out by passing from level $p$ in weight $2$ to level one in weight $4$: a cusp form whose coefficients are congruent modulo $m$ to $af(1)$ times the divisor-sum $\sigma'_p$ gives rise to a weight-four level-one form, and the resulting numerical divisibility is recorded here. It is used by [`CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo) to rule out such congruences for suitable $m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : (24 * m : ℤ) ∣ 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) := by sorry
