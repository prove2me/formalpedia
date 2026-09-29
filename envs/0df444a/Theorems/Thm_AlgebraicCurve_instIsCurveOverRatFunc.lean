-- Prove2me | Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
-- name    : AlgebraicCurve.instIsCurveOverRatFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/af5771e7-2a3e-5ee1-882a-27f33bb8eb3e
-- title:
--   The rational function field K(X) is a curve over K
-- statement:
--   For an arbitrary field $K$, the extension $K \subseteq K(X)$, with $K(X)$ the field `RatFunc K` of rational functions in one variable, satisfies the project's predicate [`AlgebraicCurve.IsCurveOver K (RatFunc K)`](def/AlgebraicCurve_IsCurveOver.html#L15). Unfolding the class, this asserts three things. First, the extension has principal divisors: for every nonzero $f \in K(X)$ there is a divisor $D$ on $K(X)/K$ whose value at each place $v$ equals $v.\mathrm{ord}\, f$, the order of $f$ at $v$, and whose degree is $0$. Here a place of $K(X)/K$ is a valuation subring of $K(X)$ that contains the image of $K$, is not all of $K(X)$, and is a principal ideal ring. Second, residue fields are finite over the base: for every such place $v$, the residue field of the local ring $v$ is a finite-dimensional $K$-module. Third, the module of Kähler differentials $\Omega_{K(X)/K}$ is free as a $K(X)$-module and its rank over $K(X)$ is $1$. Since `IsCurveOver` is a `Prop`-valued class, the statement is available as an instance for $K(X)$ over any field $K$.
--
--   This is the statement that the rational function field, the function field of $\mathbb{P}^1_K$, is a curve over $K$ in the sense used throughout this development, with $\Omega_{K(X)/K} = K(X)\,dX$ and $\deg(f) = 0$ for principal divisors. It discharges the `IsCurveOver K (RatFunc K)` hypothesis in the $\mathbb{P}^1$ computations downstream, among them the determination of a canonical divisor and of the genus of $K(X)$, and the Riemann–Roch statements applied to the rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_instIsCurveOverRatFunc.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.instIsCurveOverRatFunc (K : Type*) [Field K] :
    AlgebraicCurve.IsCurveOver K (RatFunc K) := by sorry
