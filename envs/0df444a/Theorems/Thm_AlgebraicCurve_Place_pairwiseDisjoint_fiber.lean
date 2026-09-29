-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_pairwiseDisjoint_fiber
-- name    : AlgebraicCurve.Place.pairwiseDisjoint_fiber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/41fc2ab7-0811-5b09-8b39-6ca2b714072b
-- title:
--   Fibres of places over distinct base places are disjoint
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the two $K$-structures being compatible (scalar tower), and assume $F'$ is integral over $F$ and that $F'/K$ has principal divisors, i.e. for every $f \in F'$ with $f \neq 0$ there is a finitely supported function $D$ from the places of $F'/K$ to $\mathbb{Z}$ with $D(w) = \operatorname{ord}_w(f)$ at every place $w$ and $\deg D = 0$, where the degree is the sum of the $D(w)$ weighted by the residue degrees. Here a place of a field extension $F/K$ is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and whose ring is a principal ideal ring. Given a finite set $s$ of places of $F/K$, the assertion is that the family of finite sets $v \mapsto v.\mathrm{fiber}\ F'$, consisting of the places of $F'/K$ restricting to $v$ on $F$, is pairwise disjoint over $s$: for distinct $v_1, v_2 \in s$ the finsets $v_1.\mathrm{fiber}\ F'$ and $v_2.\mathrm{fiber}\ F'$ have no common element.
--
--   This is the bookkeeping statement that the fibres of the restriction map on places of $F'/K$ over distinct places of $F/K$ do not meet, a place of $F'$ having a single restriction to $F$; the integrality and principal-divisor hypotheses are what make each fibre a finite set. It is used to split a product or sum indexed by the places of $F'$ above a finite set of places of $F$ into the separate fibrewise contributions, as in [`AlgebraicCurve.Divisor.evalFun_pullback`](thm.html#AlgebraicCurve.Divisor.evalFun_pullback) and [`AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable`](thm.html#AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_pairwiseDisjoint_fiber.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.pairwiseDisjoint_fiber {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by sorry
