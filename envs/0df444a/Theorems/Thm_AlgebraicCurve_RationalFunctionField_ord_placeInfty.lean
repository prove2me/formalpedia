-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty
-- name    : AlgebraicCurve.RationalFunctionField.ord_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3c1d2f21-1efb-5e11-a4c3-ce8ddea9179b
-- title:
--   Order at the infinite place is minus the degree
-- statement:
--   Let $K$ be a field and let $f$ be a nonzero element of the rational function field $\mathrm{RatFunc}\,K$. Consider the place $\mathrm{placeInfty}\,K$ of $\mathrm{RatFunc}\,K$ over $K$: in the project's sense a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$ under the structure map, different from all of $F$, and a principal ideal ring; for $\mathrm{placeInfty}\,K$ the valuation subring is the one attached to the infinity valuation $\mathrm{RatFunc.inftyValuation}\,K$ on $K(t)$, whose containment of the constants comes from the triviality of that valuation on $K$, whose non-triviality gives that it is not everything, and whose principality comes from the fact that the valuation ring is a discrete valuation ring. For a place $v$ the integer $v.\mathrm{ord}\,g$ is defined as $-\log$ of the value at $g$ of the adic valuation of the height-one prime of the valuation subring, with values in $\mathbb{Z}^{m0}$. The assertion is the equality $(\mathrm{placeInfty}\,K).\mathrm{ord}\,f = -f.\mathrm{intDegree}$, where the integer degree of $f$ is the degree of its numerator minus that of its denominator.
--
--   This identifies the normalised order function at the place at infinity of $\mathbb{P}^1_K$ with minus the degree of a rational function; in particular a polynomial of degree $d$ has a pole of order $d$ there, and $1/t$ is a uniformiser. It is used throughout the function-field foundations of the project, for instance in determining which rational functions lie in $K[t]$ away from infinity and in the finiteness and Riemann–Roch computations for the rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean

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

theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree := by sorry
