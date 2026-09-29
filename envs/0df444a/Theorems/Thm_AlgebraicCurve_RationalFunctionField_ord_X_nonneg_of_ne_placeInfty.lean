-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty
-- name    : AlgebraicCurve.RationalFunctionField.ord_X_nonneg_of_ne_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3595a982-deb4-5e3e-abf1-28ca3a6013a2
-- title:
--   ordᵤ(X)≥ 0 for every place u≠∞ of K(X)
-- statement:
--   Let $K$ be a field and let $u$ be a place of the rational function field $\mathrm{RatFunc}\,K$ over $K$, that is, a valuation subring of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, is not the whole of $\mathrm{RatFunc}\,K$, and is a principal ideal ring. Assume that $u$ is not the place `RationalFunctionField.placeInfty K`, the place whose valuation subring is the valuation subring of the infinite (degree) valuation `RatFunc.inftyValuation K` on $\mathrm{RatFunc}\,K$. Then $0 \le u.\mathrm{ord}\,X$, where for $f \in \mathrm{RatFunc}\,K$ the integer $u.\mathrm{ord}\,f$ is defined as $-\log$ of the value of $f$ under the adic valuation attached to the height-one prime of the valuation subring of $u$, with values in $\mathbb{Z}^{m0}$. In other words, the coordinate function $X$ has non-negative order, hence no pole, at every place of $K(X)/K$ other than the place at infinity.
--
--   This is the standard statement that $X$ is regular away from the infinite place of the rational function field, the pole of $X$ being concentrated at $\infty$ with $\operatorname{ord}_\infty(X) = -1$. It enters the construction of the canonical transcendence tower over $K(X)$ and is used in the bound [`AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable`](thm.html#AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_X_nonneg_of_ne_placeInfty.lean

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

theorem RationalFunctionField.ord_X_nonneg_of_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by sorry
