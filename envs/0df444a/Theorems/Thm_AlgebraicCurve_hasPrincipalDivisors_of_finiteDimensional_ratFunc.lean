-- Prove2me | Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc
-- name    : AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/3fde7f9d-303a-5407-a61d-b831a4913e3d
-- title:
--   Principal divisors of degree zero on finite extensions of K(X)
-- statement:
--   Let $K$ be a field of characteristic $0$ and let $F'$ be a field carrying a $K$-algebra structure and a $K(X)$-algebra structure (for $K(X) =$ `RatFunc K` the rational function field), compatible in the sense that $K \to K(X) \to F'$ is a scalar tower, and such that $F'$ is finite-dimensional over $K(X)$. The conclusion is `HasPrincipalDivisors K F'`: for every $f \in F'$ with $f \neq 0$ there is a divisor $D$, that is, a finitely supported function from the places of $F'$ over $K$ to $\mathbb{Z}$, such that $D(v) = v.\mathrm{ord}\,f$ for every place $v$ and such that $\mathrm{degree}\,D = \sum_v D(v)\cdot v.\mathrm{deg} = 0$. Here a place of $F'$ over $K$, in the project's sense, is a valuation subring $\mathcal{O}_v \subseteq F'$ containing $\mathrm{algebraMap}\,K\,F'(a)$ for every $a \in K$, distinct from all of $F'$, and a principal ideal ring; $v.\mathrm{ord}$ is the associated order function on $F'$ and $v.\mathrm{deg}$ the associated degree of $v$. Since $D$ is finitely supported, the first clause in particular asserts that $f$ has nonzero order at only finitely many places.
--
--   This is the statement that on an algebraic curve every nonzero rational function has a well-defined divisor, of degree zero — classically the product formula $\sum_v \operatorname{ord}_v(f)\deg v = 0$ for a function field of one variable, here asserted only for fields finite over $K(X)$ with $K$ of characteristic zero. It supplies the divisor-theoretic input to [`WeierstrassCurve.Affine.hasPrincipalDivisors_functionField`](thm.html#WeierstrassCurve.Affine.hasPrincipalDivisors_functionField) and, through it, to the injectivity statement [`AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible`](thm.html#AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc (K : Type*) [Field K] [CharZero K] (F' : Type*)
    [Field F'] [Algebra K F'] [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F'] :
    HasPrincipalDivisors K F' := by sorry
