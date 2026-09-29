-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional
-- name    : AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8d6abb0c-e134-5f13-b229-4a15c978b445
-- title:
--   Finiteness of zeros and poles in a finite separable extension of K(X)
-- statement:
--   Let $K$ be a field and let $F'$ be a field equipped with a $K$-algebra structure and with a $\mathrm{RatFunc}\,K$-algebra structure, the two being compatible (a scalar tower $K \subseteq K(X) \subseteq F'$), and assume $F'$ is finite-dimensional over the rational function field $K(X)$ and separable over it. Let $f \in F'$ be nonzero. Then the set of places $w$ of $F'$ over $K$ with $\operatorname{ord}_w(f) \neq 0$ is finite. Here a place of $F'$ over $K$ is, as defined in this development, a valuation subring of $F'$ which contains the image of $K$ under the structure map, is not the whole of $F'$, and is a principal ideal ring; for such a $w$ the quantity $\operatorname{ord}_w(f)$ is $-\log$ of the value at $f$ of the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of the valuation subring of $w$, so that $\{w : \operatorname{ord}_w(f) \neq 0\}$ is the set of zeros and poles of $f$.
--
--   This is the classical statement that a nonzero element of an algebraic function field has only finitely many zeros and poles, here in the form needed for function fields that are finite separable extensions of $K(X)$. It is the finiteness ingredient used by [`AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`](thm.html#AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable), which produces principal divisors for such fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']
    {f : F'} (hf : f ≠ 0) : {w : Place K F' | w.ord f ≠ 0}.Finite := by sorry
