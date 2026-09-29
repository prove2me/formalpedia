-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
-- name    : AlgebraicCurve.Place.ord_add_eq_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/aa3e68f5-2bd7-5b6e-b609-302cb070c32a
-- title:
--   Strict ultrametric equality: ord(f+g)=ord f
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project: a valuation subring of $F$ that contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. Associated with $v$ is the $\mathbb{Z}^{m0}$-valued adic valuation [`AlgebraicCurve.Place.adicValuation`](def/AlgebraicCurve_DivisorClassGroup.html#L102), namely the valuation attached to the height-one prime of $v$, and the integer-valued order function [`AlgebraicCurve.Place.ord`](def/AlgebraicCurve_DivisorClassGroup.html#L122), defined on $f \in F$ as minus the `WithZero` logarithm of the value of that adic valuation at $f$. Let $f, g \in F$ be nonzero and assume $\operatorname{ord}_v(f) < \operatorname{ord}_v(g)$. The conclusion is $\operatorname{ord}_v(f+g) = \operatorname{ord}_v(f)$. The two non-vanishing hypotheses are needed because the order function takes the value $0$ at $0$, so that without them the comparison of orders would not reflect a comparison of valuations.
--
--   This is the equality case of the ultrametric inequality, transported from the multiplicative $\mathbb{Z}^{m0}$-valued adic valuation of a place to the additive integer order function. It is used throughout the development of orders and divisors attached to places, for instance in the construction of elements with prescribed valuations at a finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ord_add_eq_of_lt.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Place.ord_add_eq_of_lt {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by sorry
