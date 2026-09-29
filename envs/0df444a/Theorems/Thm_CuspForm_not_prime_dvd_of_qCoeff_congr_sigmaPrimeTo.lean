-- Prove2me | Theorems.Thm_CuspForm_not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/215dc071-4c8d-5430-9843-4fe4f109e077
-- title:
--   A prime p cannot divide the Eisenstein modulus
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $m \ge 2$. Let $f$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(p)$, and let $af : \mathbb{N} \to \mathbb{Z}$ be a sequence of integers which represents the $q$-expansion coefficients of $f$, in the sense that for every $n$ the image of $af\,n$ in $\mathbb{C}$ equals [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19), the $n$-th coefficient of the $q$-expansion of $f$ taken with width $1$. Assume that $af\,1$ and $m$ are coprime as elements of $\mathbb{Z}$ (in the Bézout sense of `IsCoprime`), and that the Eisenstein congruence holds: for every $n \ne 0$, $m$ divides $af\,n - \sigma'_p(n)\,af\,1$ in $\mathbb{Z}$, where $\sigma'_p(n) = \sum_{d \mid n,\ p \nmid d} d$ is the sum of the divisors of $n$ prime to $p$ (`sigmaPrimeTo p n`). The conclusion is that $p$ does not divide $m$ as natural numbers.
--
--   This is the statement that the residual characteristic of an Eisenstein-type congruence for weight-two cusp forms on $\Gamma_0(p)$ cannot be $p$ itself; in Mazur's work on the Eisenstein ideal the corresponding case is handled by a different argument. It is used in the further arithmetic consequences of the congruence, [`CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo) and [`CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : ¬ (p ∣ m) := by sorry
