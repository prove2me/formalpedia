-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
-- name    : AlgebraicCurve.Place.evalAt_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/9189b191-17b0-53c0-9c16-e7bdb3ea4356
-- title:
--   Nonvanishing of the value at a rational place of a function of order zero
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal{O}_v =$ `v.toValuationSubring` of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational in the sense of the predicate `IsRational`, namely that the induced map from $K$ to the residue field $\mathcal{O}_v/\mathfrak{m}_v$ is surjective. Let $f \in F$ be nonzero and suppose that $\operatorname{ord}_v(f) = 0$, where $\operatorname{ord}_v(f)$ is minus the logarithm of the value of $f$ under the valuation attached to the height one prime of $\mathcal{O}_v$. Then the value $\operatorname{evalAt}_v(f) \in K$ is nonzero, where $\operatorname{evalAt}_v(f)$ is defined to be a chosen preimage in $K$, under the map $K \to \mathcal{O}_v/\mathfrak{m}_v$, of the residue class of $f$ when $f \in \mathcal{O}_v$, and $0$ otherwise (so that the value is, in particular, a genuine preimage exactly when $v$ is rational and $f$ lies in $\mathcal{O}_v$).
--
--   This is the statement that a nonzero function with neither a zero nor a pole at a rational place has nonzero value there; equivalently, a nonzero element of order zero is a unit of the local ring and so has nonzero residue. It underlies the evaluation of functions at divisors, $f(D) = \prod_v f(v)^{D(v)}$, being nonzero when the divisor avoids the support of $\operatorname{div} f$, and is used throughout the evaluation-at-divisors layer, for instance by [`AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward`](thm.html#AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_ne_zero.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0) : v.evalAt f ≠ 0 := by sorry
