-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero
-- name    : AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/fdb7c420-9420-59be-b0d3-d85ceb56a7ea
-- title:
--   A nonzero rational function has finitely many zeros and poles
-- statement:
--   Let $K$ be a field and let $f$ be a nonzero element of the field $K(t)$ of rational functions in one variable over $K$. A place of $K(t)$ over $K$, in the sense used here, is a valuation subring $\mathcal{O}$ of $K(t)$ which contains the image of $K$ under the structure map, is not the whole of $K(t)$, and is a principal ideal ring; to such a place is attached the $\mathbb{Z}^{m0}$-valued adic valuation of $K(t)$ coming from the corresponding height-one prime of $\mathcal{O}$, and $\operatorname{ord}_v(g) \in \mathbb{Z}$ is defined as minus the logarithm of the value of that valuation at $g$ (so $\operatorname{ord}_v$ is the normalised valuation attached to $v$, positive at a zero and negative at a pole, with the convention $\operatorname{ord}_v(0) = 0$). The assertion is that the set of places $v$ of $K(t)$ over $K$ with $\operatorname{ord}_v(f) \neq 0$ is a finite set.
--
--   This is the finiteness of the support of the divisor of a nonzero rational function on $\mathbb{P}^1_K$: the zeros and poles of $f$ are contained in the primes dividing its numerator or denominator, together with the place at infinity. It is the finite-support half of the existence of principal divisors for $K(t)$, and is used in the computation of divisor degrees on $\mathbb{P}^1_K$, in particular in the results on degrees of places and on functions with prescribed order.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero {K : Type*} [Field K] {f : RatFunc K} (hf : f ≠ 0) : {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by sorry
