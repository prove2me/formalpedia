-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula
-- name    : AlgebraicCurve.Divisor.pushforwardNormFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/c9831641-b6b4-5dfc-bb99-5334e405eccd
-- title:
--   Push-forward of a principal divisor is the norm
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the three structures forming a scalar tower, with $F'/F$ finite-dimensional and separable, $F$ of characteristic zero, and assume `HasPrincipalDivisors K F'`, i.e. every nonzero $f \in F'$ admits a divisor $D$ (a finitely supported $\mathbb{Z}$-valued function on the places of $F'$ over $K$, a place being a valuation subring of $F'$ that contains the image of $K$, is not all of $F'$ and is a principal ideal ring) whose value at every place $w$ is $w.\mathrm{ord}\, f$ and whose degree $\sum_w D(w)\cdot \deg w$ vanishes. Then `Divisor.PushforwardNormFormula K F F'` holds: for every nonzero $f \in F'$, every divisor $D$ on the places of $F'$ over $K$ with $D(w) = w.\mathrm{ord}\, f$ for all $w$, and every place $v$ of $F$ over $K$, the push-forward of $D$ — the additive map sending a place $w$ to its restriction $w|_F$ weighted by the inertia degree of $w$ over $F$, so that its value at $v$ is $\sum_{w|_F = v} f(w|v)\, D(w)$ — takes at $v$ the value $v.\mathrm{ord}\big(N_{F'/F}(f)\big)$, the order at $v$ of the relative norm `Algebra.norm F f`.
--
--   This is the classical compatibility of the inertia-weighted push-forward (norm) of divisors with the field norm, $\pi_*(\operatorname{div} f) = \operatorname{div}(N_{F'/F} f)$, for a finite separable extension of function fields. It is used to show that the push-forward carries principal divisors to principal divisors, and hence descends to divisor class groups, via [`AlgebraicCurve.Divisor.pushforward_div`](thm.html#AlgebraicCurve.Divisor.pushforward_div) and [`AlgebraicCurve.normFormulaAlong`](thm.html#AlgebraicCurve.normFormulaAlong).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_pushforwardNormFormula.lean

import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.pushforwardNormFormula {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F'] : Divisor.PushforwardNormFormula K F F' := by sorry
