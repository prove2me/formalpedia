-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback_of_isPurelyInseparable
-- name    : AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/dede09fd-8379-56a1-b32f-c32a1ff4fd72
-- title:
--   Evaluation of f on a pullback divisor equals evaluation of N(f)
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$ and an $F$-algebra structure on $F'$ forming a scalar tower, with $F'$ finite-dimensional over $F$ and purely inseparable over it; assume that every nonzero element of $F'$ has a principal divisor of degree $0$, i.e. a finitely supported integer-valued function on the places of $F'$ whose value at each place $w$ is $\operatorname{ord}_w$ of that element and whose degree is zero, and assume the fundamental identity over $K$: for every place $v$ of $F$, $\sum_{w \in \text{fibre of } v} e(w/F)\,\deg w = [F':F]\,\deg v$. Here a place is a valuation subring of the field containing the image of $K$, proper, and a principal ideal ring. Let $f \in F'$ be nonzero and let $E$ be a divisor on $F$, such that every $v$ in the support of $E$ is rational (the map from $K$ to the residue field of $v$ is surjective), every place $w$ of $F'$ lying over such a $v$ is rational, and $\operatorname{ord}_w f = 0$ for every such $w$. Then $\prod_w \operatorname{ev}_w(f)^{(\text{pullback of } E)(w)} = \prod_v \operatorname{ev}_v(N_{F'/F} f)^{E(v)}$, where the pullback of $E$ assigns to $w$ over $v$ the value $E(v)\,e(w/F)$, and $\operatorname{ev}_u(g) \in K$ is the preimage in $K$ of the residue of $g$ when $g$ lies in the valuation ring of $u$, and $0$ otherwise.
--
--   This is the purely inseparable case of the Weil reciprocity style identity $f(u^{*}E) = N_{F'/F}(f)(E)$ for evaluation of functions against divisors; here one place lies over each $v$, with ramification index $[F':F]$, and the norm is the corresponding power of $f$. It is used to prove the adjointness of pullback and pushforward for the pairing attached to a Weil datum along a purely inseparable morphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_evalFun_pullback_of_isPurelyInseparable.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.evalFun_pullback_of_isPurelyInseparable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [IsPurelyInseparable F F'] [HasPrincipalDivisors K F'] [FundamentalIdentity K F F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F) (hrat : ∀ v ∈ E.support, Place.IsRational v) (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by sorry
