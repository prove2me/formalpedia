-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq
-- name    : AlgebraicCurve.RationalFunctionField.evalAt_placeInfty_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/2394ee35-85ca-5803-8ea5-008e161f3919
-- title:
--   Value at infinity: f(∞)=c when deg(f-c)<0
-- statement:
--   Let $K$ be a field, let $f \in K(t) =$ `RatFunc K` be a rational function and let $c \in K$ be a constant, and suppose that either $f - c = 0$ (where $c$ is viewed in $K(t)$ via the structure map of $K$) or that the integer degree `intDegree` of $f - c$, i.e. the degree of its numerator minus the degree of its denominator, is strictly negative. Then the value of $f$ at the place at infinity of $K(t)$ is $c$. Here `placeInfty K` is the place of $K(t)$ over $K$ whose valuation subring is the valuation subring of the infinite-place valuation `RatFunc.inftyValuation K` (constants lie in it, it is not all of $K(t)$, and it is a principal ideal ring); and for a place $v$ the evaluation $v.\mathrm{evalAt}(f)$ is defined to be the image of the residue class of $f$ in the residue field of the valuation subring under a fixed left inverse (`Function.invFun`) of the structure map $K \to v.\mathrm{ResidueField}$ when $f$ belongs to the valuation subring, and $0$ otherwise. Thus the assertion is that $f$ is regular at infinity and that the chosen preimage of its residue there is exactly $c$.
--
--   This is the concrete formula for evaluation at the place at infinity of the rational function field: a rational function whose numerator degree does not exceed its denominator degree takes at $\infty$ the value of the constant it approximates, the ratio of leading coefficients (or $0$). It is used to compute values such as $\bigl((t-a)/(t-a_0)\bigr)(\infty) = 1$, and is invoked in the construction of chart data for modular curves in [`ModularCurve.exists_chartData_of_lineResidues`](thm.html#ModularCurve.exists_chartData_of_lineResidues).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq.lean

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

theorem AlgebraicCurve.RationalFunctionField.evalAt_placeInfty_eq (K : Type*) [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} {c : K} (h : f - algebraMap K (RatFunc K) c = 0 ∨ (f - algebraMap K (RatFunc K) c).intDegree < 0) : (placeInfty K).evalAt f = c := by sorry
