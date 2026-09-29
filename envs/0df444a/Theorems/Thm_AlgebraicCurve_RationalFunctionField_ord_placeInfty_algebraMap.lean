-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
-- name    : AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/46a8360b-25ea-521c-a346-d4c9dd16f8eb
-- title:
--   Order at infinity of a polynomial is -deg q
-- statement:
--   Let $K$ be a field and let $q \in K[t]$ be a non-zero polynomial. Consider the place at infinity $\mathtt{placeInfty}\,K$ of the rational function field $K(t)$: in the sense of the project's notion of a place of $K(t)$ over $K$, it is given by the valuation subring of the infinity valuation `RatFunc.inftyValuation K` on $K(t)$, which contains the image of $K$, is not all of $K(t)$, and is a principal ideal ring. For a place $v$, $v.\mathtt{ord}(f)$ is defined as minus the `WithZero`-logarithm of the value of $f$ under the adic valuation attached to the height-one prime of the valuation subring of $v$, so that it is the usual normalised order of vanishing, negative at a pole. The assertion is that for the image of $q$ under the structure map $K[t] \to K(t)$ one has $$(\mathtt{placeInfty}\,K).\mathtt{ord}\bigl(\mathrm{alg}(q)\bigr) = -\,\deg q,$$ the degree being `Polynomial.natDegree` viewed as an integer; equivalently, a non-zero polynomial of degree $d$ has a pole of order exactly $d$ at infinity.
--
--   This is the computation of the divisor of a polynomial at the point at infinity of $\mathbb{P}^1$, in the standard description of the places of $K(t)$ as the monic irreducibles together with $\infty$. It is part of the function-field foundations used in the genus-zero computations for $K(t)$ and in the local analysis of orders at places, for instance in [`AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero`](thm.html#AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.lean

import Mathlib
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap {K : Type*} [Field K] [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by sorry
