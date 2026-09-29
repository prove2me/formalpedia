-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists
-- name    : AlgebraicCurve.RationalFunctionField.stichtenothGenusExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/e80183c7-3748-5ae2-ad67-16395a9668d5
-- title:
--   Existence of the genus for separable extensions of K(X)
-- statement:
--   Let $K$ be a field and let $F$ be a field that is simultaneously a $K$-algebra and a $\mathrm{RatFunc}\,K$-algebra, compatibly (scalar tower $K \subseteq K(X) \subseteq F$), with $F$ finite-dimensional and separable over the rational function field $\mathrm{RatFunc}\,K$. Assume `IsCurveOver K F`: principal divisors exist (every $f \in F^{\times}$ admits a finitely supported $D : \mathrm{Place}\,K\,F \to \mathbb{Z}$ with $D(v) = v.\mathrm{ord}\,f$ at every place and $\deg D = 0$), every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring. Assume further `ConstantsAreBase K F`, i.e. the Riemann–Roch space $L(0)$ of the zero divisor equals the image of $K$ in $F$ under the structure map. The conclusion is `StichtenothGenusExists K F`: the set of places of $F$ over $K$ is nonempty; $L(0)$ is finite-dimensional over $K$; and there exist $\gamma \in \mathbb{Z}$ and a divisor $D_0$ such that $L(D_0)$ is finite-dimensional over $K$, $\deg D_0 - \ell(D_0) = \gamma - 1$ with $\ell$ the $K$-dimension of the Riemann–Roch space, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$.
--
--   This is the existence of the genus in Stichtenoth's form: the quantity $\deg D - \ell(D)$ is bounded above over all divisors and the bound is attained, which is equivalent to Riemann's inequality $\ell(D) \ge \deg D + 1 - \gamma$ together with equality at some $D_0$. It is the input, for function fields presented as finite separable extensions of $K(X)$, to the adelic Riemann–Roch theorem and the rank-one statement for Weil differentials, and is cited by [`AlgebraicCurve.exists_genus_riemannIndex_of_isCurveOver`](thm.html#AlgebraicCurve.exists_genus_riemannIndex_of_isCurveOver), [`AlgebraicCurve.stichtenothGenusExists_of_isCurveOver`](thm.html#AlgebraicCurve.stichtenothGenusExists_of_isCurveOver) and [`AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver`](thm.html#AlgebraicCurve.weilDifferentialRankOne_of_isCurveOver).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem RationalFunctionField.stichtenothGenusExists (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F := by sorry
