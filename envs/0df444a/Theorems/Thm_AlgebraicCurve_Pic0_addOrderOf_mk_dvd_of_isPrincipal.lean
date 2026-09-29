-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal
-- name    : AlgebraicCurve.Pic0.addOrderOf_mk_dvd_of_isPrincipal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/070fa8d4-06f3-50d5-8dd3-8f0809acc39f
-- title:
--   Order of a divisor class divides m when mD is principal
-- statement:
--   Let $K \subseteq F$ be fields, $F$ a $K$-algebra. A place of $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, its degree is the sum of its values weighted by the residue degrees $v.\mathrm{deg}$, and $\mathrm{Divisor.degZero}$ is the subgroup of divisors of degree $0$. A divisor $E$ is principal when there is a nonzero $f \in F$ with $E(v) = v.\mathrm{ord}(f)$ for every place $v$; the principal divisors form a subgroup, and $\mathrm{Pic0}$ is the quotient of $\mathrm{Divisor.degZero}$ by the intersection of that subgroup with the degree-zero divisors, with $\mathrm{Pic0.mk}$ the quotient map. The assertion: given a degree-zero divisor $D$ of $F/K$ and a natural number $m$ such that the divisor $m \bullet D$ (the underlying divisor of $D$, scaled by $m$) is principal, the additive order of the class $\mathrm{Pic0.mk}\,D$ divides $m$. Since $\mathrm{addOrderOf}$ is $0$ for elements of infinite additive order, the case $m = 0$ carries no information.
--
--   This is the standard bookkeeping step converting a function with prescribed divisor into a bound on the order of a divisor class: exhibiting $f \in F^{\times}$ with $\mathrm{div}(f) = mD$ shows that the order of $[D]$ in $\mathrm{Pic}^0(F/K)$ divides $m$. It is used in the treatment of cuspidal divisor classes on modular curves, for instance by [`ModularCurve.addOrderOf_cuspidalClass_dvd`](thm.html#ModularCurve.addOrderOf_cuspidalClass_dvd) and [`ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator`](thm.html#ModularCurve.addOrderOf_cuspidalClass_eq_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.addOrderOf_mk_dvd_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : addOrderOf (Pic0.mk D) ∣ m := by sorry
