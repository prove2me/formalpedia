-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_weilReciprocity
-- name    : AlgebraicCurve.RationalFunctionField.weilReciprocity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5f438ffc-3d51-56cb-9013-e7f63fc633f1
-- title:
--   Weil reciprocity for the rational function field
-- statement:
--   Let $K$ be an algebraically closed field and let $F = \mathrm{RatFunc}\ K$ be its field of rational functions, regarded as a $K$-algebra. The assertion is the predicate `WeilReciprocity K (RatFunc K)`, namely: for all $f, g \in \mathrm{RatFunc}\ K$ and all divisors $D_f, D_g$ — that is, finitely supported functions from the places of $\mathrm{RatFunc}\ K$ over $K$ to $\mathbb{Z}$, a place being a valuation subring of $\mathrm{RatFunc}\ K$ that contains the image of $K$, is not the whole field, and is a principal ideal ring — if $f \neq 0$, $g \neq 0$, if $D_f(v) = \mathrm{ord}_v f$ and $D_g(v) = \mathrm{ord}_v g$ for every place $v$, if for every place $v$ at least one of $\mathrm{ord}_v f$ and $\mathrm{ord}_v g$ vanishes (so the two divisors have disjoint supports), and if every place in the support of $D_f$ and every place in the support of $D_g$ is rational in the sense that $K$ surjects onto its residue field, then $\mathrm{evalFun}\ f\ D_g = \mathrm{evalFun}\ g\ D_f$, where $\mathrm{evalFun}\ h\ D$ denotes the finite product $\prod_{v} (\mathrm{evalAt}_v\ h)^{D(v)} \in K$ over the support of $D$. Thus $\prod_v f(v)^{\mathrm{ord}_v g} = \prod_v g(v)^{\mathrm{ord}_v f}$, with no sign.
--
--   This is Weil's reciprocity law for $\mathbb{P}^1_K$, the case of the rational function field, stated in the symmetric form without the sign $(-1)^{\deg f \deg g}$ of the affine resultant identity (that sign is contributed by the place at infinity, which the disjointness hypothesis excludes). It serves as the base case from which reciprocity on a general curve is obtained by norm along a finite map to $\mathbb{P}^1$, and is cited by [`AlgebraicCurve.weilReciprocity`](thm.html#AlgebraicCurve.weilReciprocity) and [`AlgebraicCurve.weilReciprocity_of_isAlgClosed`](thm.html#AlgebraicCurve.weilReciprocity_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_weilReciprocity.lean

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

theorem AlgebraicCurve.RationalFunctionField.weilReciprocity (K : Type*) [Field K] [IsAlgClosed K] : WeilReciprocity K (RatFunc K) := by sorry
