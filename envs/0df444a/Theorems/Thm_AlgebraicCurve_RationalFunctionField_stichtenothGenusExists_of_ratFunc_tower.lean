-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower
-- name    : AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/9d403461-ddf0-59f2-9bae-4b9855c6303a
-- title:
--   Riemann's theorem over a rational function subfield
-- statement:
--   Let $K$ be a field and let $F$ be a field that is simultaneously an algebra over $K$ and over the rational function field $\mathrm{RatFunc}\,K$, compatibly (a scalar tower $K \subseteq \mathrm{RatFunc}\,K \subseteq F$), with $F$ finite-dimensional and separable over $\mathrm{RatFunc}\,K$. Assume the principal divisor hypothesis [`AlgebraicCurve.HasPrincipalDivisors K F`](def/AlgebraicCurve_DivisorClassGroup.html#L217): every $f \in F^{\times}$ admits a finitely supported divisor $D : \mathrm{Place}\,K\,F \to \mathbb{Z}$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and $\deg D = 0$, where a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, and $\deg$ is the sum of the coefficients weighted by the residue degrees. Assume also [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15): the above, together with finiteness of every residue field $v.\mathrm{ResidueField}$ over $K$ and freeness of $\Omega_{F/K}$ over $F$ of rank $1$. Finally assume that $F$ has at least one place and that the Riemann–Roch space $L(0) = \{f \in F : v(f) \le 1 \text{ for all } v\}$ is finite-dimensional over $K$. The conclusion is [`AlgebraicCurve.StichtenothGenusExists K F`](def/AlgebraicCurve_AdelicIndex.html#L419): $F$ has a place, $L(0)$ is finite-dimensional over $K$, and there exist $\gamma \in \mathbb{Z}$ and a divisor $D_0$ such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$.
--
--   This is Riemann's theorem in Stichtenoth's formulation: for a curve presented as a finite separable extension of $K(X)$, the quantity $\deg D - \ell(D)$ is bounded above over all divisors and attains its supremum, so that a genus $\gamma$ with $\ell(D) \ge \deg D + 1 - \gamma$ for all $D$, with equality at some $D_0$, exists. It supplies the `StichtenothGenusExists` hypothesis for the Riemann index formula and the Riemann–Roch results used for curves given over a rational function field, and is invoked for two-chart integral models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower (K : Type*) [Field K]
    [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [AlgebraicCurve.IsCurveOver K F] [Nonempty (AlgebraicCurve.Place K F)]
    [FiniteDimensional K (AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))] :
    AlgebraicCurve.StichtenothGenusExists K F := by sorry
