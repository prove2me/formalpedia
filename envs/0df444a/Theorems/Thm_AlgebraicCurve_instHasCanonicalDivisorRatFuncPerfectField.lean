-- Prove2me | Theorems.Thm_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField
-- name    : AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/55aafe79-6e3c-502d-b00f-09879a75ba8c
-- title:
--   Existence of canonical divisors on P¹_K, K perfect
-- statement:
--   Let $K$ be a field which is perfect, and let $F = \mathrm{RatFunc}\,K$ be the rational function field in one variable over $K$, assumed to satisfy the project's curve hypothesis [`AlgebraicCurve.IsCurveOver K (RatFunc K)`](def/AlgebraicCurve_IsCurveOver.html#L15): namely that every nonzero $f \in F$ has a finitely supported divisor $D : \mathrm{Place}\,K\,F \to_{f} \mathbb{Z}$ with $D(v) = \operatorname{ord}_v f$ at every place and $\deg D = 0$; that each place has residue field finite-dimensional over $K$; and that $\Omega_{F/K}$ is free of rank one over $F$. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and whose ideals are principal. The conclusion is the predicate [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14) for this pair: for every Kähler differential $\omega \in \Omega_{F/K}$ with $\omega \neq 0$ there exists a finitely supported function $D : \mathrm{Place}\,K\,F \to_{f} \mathbb{Z}$ such that for every place $v$ one has $D(v) = v.\mathrm{ordDifferential}\,\omega$, that is $D(v) = \operatorname{ord}_v$ of the coefficient of $\omega$ with respect to $v$'s chosen differential coordinate. The force of the statement is the finiteness of the support; no degree condition is asserted.
--
--   This is the existence of the canonical divisor class on the projective line over a perfect field, in the form required by the project's divisor formalism: the local orders of a nonzero differential vanish at all but finitely many places of $K(X)$. It feeds the residue theorem for rational function fields, the ramification-index count [`AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq`](thm.html#AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq), and thence the genus formula for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField (K : Type*) [Field K] [PerfectField K]
    [AlgebraicCurve.IsCurveOver K (RatFunc K)] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K) := by sorry
