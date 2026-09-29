-- Prove2me | Theorems.Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
-- name    : CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2792e208-01d1-53ad-a3f4-f3ce15b04e66
-- title:
--   Vanishing of a cusp form supported on multiples of p ∤ m
-- statement:
--   Let $m$ and $p$ be natural numbers with $m \neq 0$, let $p$ be prime and suppose $p \nmid m$. Let $F$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(m)$ of $\mathrm{SL}_2(\mathbb{Z})$ (as a subgroup of $\mathrm{GL}_2(\mathbb{R})$), i.e. an element of `CuspForm (CongruenceSubgroup.Gamma0 m) 2`. Write $a_n(F)$ for the $n$-th coefficient of the $q$-expansion of $F$ of width $1$, that is, [`ModularFormClass.qCoeff F n`](def/FLTPrelim_Modularity.html#L19) is the coefficient of $q^n$ in `qExpansion 1 F`. The hypothesis is that $a_n(F) = 0$ for every natural number $n$ not divisible by $p$; note that this includes $n = 0$ only when $p \nmid 0$ fails, so the condition is imposed exactly at those $n$ prime to the divisibility by $p$, and in particular at $n = 1$. The conclusion is that $F$ is the zero cusp form.
--
--   This is the half of Atkin–Lehner's lemma on forms supported on multiples of a fixed integer in the case where that integer is a prime not dividing the level: a cusp form of weight $2$ and level $m$ whose $q$-expansion is concentrated on multiples of such a prime $p$ vanishes identically. It is used in the study of the Hecke action on cusp forms of level $\Gamma_0(m)$, notably in the lemmas on the operator $U$ and on $q$-coefficients of newforms that feed the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hpm : ¬ p ∣ m)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff F n = 0) : F = 0 := by sorry
