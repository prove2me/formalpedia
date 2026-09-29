-- Prove2me | Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
-- name    : AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/35c6278e-17b9-5e27-a1ad-5af5947dc234
-- title:
--   Degree-zero principal divisors over finite separable extensions of K(X)
-- statement:
--   Let $K$ be a field and let $F'$ be a field carrying a $K$-algebra structure and a $K(X)$-algebra structure (for $K(X) =$ `RatFunc K`) which form a scalar tower $K \subseteq K(X) \subseteq F'$, and assume $F'$ is finite-dimensional over $K(X)$ and separable over $K(X)$. The conclusion is `HasPrincipalDivisors K F'`: for every nonzero $f \in F'$ there is a finitely supported function $D$ from the places of $F'$ over $K$ to $\mathbb{Z}$ such that $D(v) = \operatorname{ord}_v(f)$ for every place $v$, and $D$ has degree zero, i.e. $\sum_v D(v)\,\deg v = 0$. Here a place of $F'$ over $K$ is, by definition, a valuation subring of $F'$ containing the image of $K$, different from all of $F'$, and a principal ideal ring; $\operatorname{ord}_v$ and $\deg v$ are the associated order function and place degree. Since $D$ is required to be finitely supported and to agree with $\operatorname{ord}_v(f)$ at every place, the assertion includes the statement that $f$ has only finitely many zeros and poles.
--
--   This is the classical theorem that a principal divisor on a function field of one variable has degree zero, in the form needed for finite separable extensions of the rational function field over an arbitrary base field $K$, so in particular in positive characteristic. It is used to obtain the divisor theory of the function field of a Weierstrass curve, being cited by [`WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or`](thm.html#WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable (K : Type*) [Field K] (F' : Type*)
    [Field F'] [Algebra K F'] [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by sorry
