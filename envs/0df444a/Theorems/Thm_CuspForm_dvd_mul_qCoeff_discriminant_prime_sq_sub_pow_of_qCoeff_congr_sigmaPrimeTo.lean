-- Prove2me | Theorems.Thm_CuspForm_dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2d10b262-db73-55f7-a430-6ad7fa0b4fce
-- title:
--   24m ∣ a₁(p-1)bigl(τ(p²)-p¹²bigr)
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $2 \le m$. Let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, and let $af : \mathbb{N} \to \mathbb{Z}$ be an integral sequence realising its $q$-expansion coefficients: for every $n$, the complex number $af(n)$ equals [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ taken with width $1$. Assume the Eisenstein congruence: for every $n \ne 0$, $m$ divides $af(n) - \sigma'_p(n)\, af(1)$, where $\sigma'_p(n) = \sum_{d \mid n,\ p \nmid d} d$ is the sum of those divisors of $n$ that are prime to $p$ (the Lean definition `sigmaPrimeTo p n`). Let $t : \mathbb{N} \to \mathbb{Z}$ likewise be an integral sequence realising the $q$-expansion coefficients of the modular discriminant $\Delta$, so that $t(n) = \tau(n)$ for all $n$. The conclusion is the divisibility, in $\mathbb{Z}$, $$24m \ \big|\ af(1)\,(p-1)\,\bigl(t(p^2) - p^{12}\bigr).$$
--
--   This is the constant-term forcing step for the Eisenstein congruence at prime level, read off at the coefficient of $q^{p^2}$: the weight-two form $f$ satisfying the congruence is paired with $\Delta$ and its Fricke transform, and the vanishing of the resulting level-one weight-fourteen trace yields the stated divisibility. It is used, together with the identity $\tau(p^2) = \tau(p)^2 - p^{11}$, to derive [`CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) (t : ℕ → ℤ) (ht : ∀ n : ℕ, (t n : ℂ) = ModularFormClass.qCoeff ModularForm.discriminant n) : (24 * m : ℤ) ∣ af 1 * ((p : ℤ) - 1) * (t (p ^ 2) - (p : ℤ) ^ 12) := by sorry
