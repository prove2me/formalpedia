-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_algebraMap_of_forall_ord_eq_zero
-- name    : AlgebraicCurve.RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/01af4f93-98fd-5cea-889f-0478a483c043
-- title:
--   Rational functions with trivial divisor are constant
-- statement:
--   Let $K$ be a field and let $g$ be a nonzero element of the rational function field $\mathrm{RatFunc}\,K$. A place of $\mathrm{RatFunc}\,K$ over $K$, in the sense used here, is a valuation subring $\mathcal{O}_v$ of $\mathrm{RatFunc}\,K$ which contains the image of $K$ under the structure map, is not the whole field, and is a principal ideal ring; for such a $v$ and an element $f$, $\operatorname{ord}_v f$ is the integer $-\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $\mathcal{O}_v$, so that $\operatorname{ord}_v f = 0$ expresses that $f$ is a unit at $v$. Assume $\operatorname{ord}_v g = 0$ for every place $v$ of $\mathrm{RatFunc}\,K$ over $K$. The conclusion is that there is a scalar $c \in K$ with $c \neq 0$ such that $g$ is the image of $c$ under the algebra map $K \to \mathrm{RatFunc}\,K$; that is, $g$ is a nonzero constant.
--
--   This is the $\mathbb{P}^1$ case, over an arbitrary base field, of the statement that an element of a function field with neither zeros nor poles is constant, equivalently that the kernel of the divisor map on $K(t)^{\times}$ is $K^{\times}$. It is used in the treatment of curve models, where it supplies the constants among the units of the rational function field, via [`AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit`](thm.html#AlgebraicCurve.CurveModel.exists_eq_appTop_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_exists_algebraMap_of_forall_ord_eq_zero.lean

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

theorem AlgebraicCurve.RationalFunctionField.exists_algebraMap_of_forall_ord_eq_zero {K : Type*} [Field K] {g : RatFunc K} (hg : g ≠ 0) (h : ∀ v : Place K (RatFunc K), v.ord g = 0) : ∃ c : K, c ≠ 0 ∧ g = algebraMap K (RatFunc K) c := by sorry
