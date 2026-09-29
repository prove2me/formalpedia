-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty
-- name    : AlgebraicCurve.RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ffaef85c-569c-56a2-ac3e-c31623f887ef
-- title:
--   Polynomials lie in every place other than ∞
-- statement:
--   Let $K$ be a field and consider the rational function field $\mathrm{RatFunc}\,K$ over $K$. A place $u$ of $\mathrm{RatFunc}\,K$ over $K$ is, by definition, a valuation subring $u.\mathrm{toValuationSubring}$ of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, is not the whole of $\mathrm{RatFunc}\,K$, and is a principal ideal ring. Let $u$ be such a place and assume $u \neq \mathrm{placeInfty}\,K$, where $\mathrm{placeInfty}\,K$ is the place whose valuation subring is that of the infinite valuation `RatFunc.inftyValuation K` on $\mathrm{RatFunc}\,K$. Then for every polynomial $q \in K[X]$, the image of $q$ under the algebra map $K[X] \to \mathrm{RatFunc}\,K$ belongs to $u.\mathrm{toValuationSubring}$. In other words, the polynomial ring is contained in the local ring of every place of $K(X)/K$ distinct from the place at infinity.
--
--   This is the statement that the coordinate function $X$, and hence every polynomial in it, is regular away from the place at infinity of the rational function field; it rests on the classification of the places of $K(X)/K$ into the places attached to the height-one primes of $K[X]$ and the place at infinity. It is used in the construction of chart data for modular curves, in [`ModularCurve.exists_chartData_of_lineResidues`](thm.html#ModularCurve.exists_chartData_of_lineResidues).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty.lean

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

theorem RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    {u : Place K (RatFunc K)} (hu : u ≠ RationalFunctionField.placeInfty K) (q : (Polynomial K)) :
    algebraMap (Polynomial K) (RatFunc K) q ∈ u.toValuationSubring := by sorry
