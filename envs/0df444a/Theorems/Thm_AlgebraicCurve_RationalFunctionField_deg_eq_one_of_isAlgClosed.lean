-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_isAlgClosed
-- name    : AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/60a99f71-0b86-5e70-95c3-986100d59d42
-- title:
--   Places of K(t) over an algebraically closed K have degree one
-- statement:
--   Let $K$ be an algebraically closed field and let $v$ be a place of the rational function field $\mathrm{RatFunc}\,K$ over $K$, that is, a structure consisting of a valuation subring $\mathcal{O}_v$ of $\mathrm{RatFunc}\,K$ together with the three conditions that $\mathcal{O}_v$ contains $\mathrm{algebraMap}\,K\,(\mathrm{RatFunc}\,K)(a)$ for every $a \in K$, that $\mathcal{O}_v$ is not the whole field, and that $\mathcal{O}_v$ is a principal ideal ring. The assertion is that $v.\mathrm{deg} = 1$, where $v.\mathrm{deg}$ is defined as the $K$-rank $\mathrm{Module.finrank}\,K$ of the residue field $\mathcal{O}_v/\mathfrak{m}_v$ of the local ring $\mathcal{O}_v$, regarded as a $K$-vector space via the structure map. Equivalently, over an algebraically closed base field every place of $K(t)$ is rational: its residue field is one-dimensional over $K$, hence equal to the image of $K$.
--
--   This is the classical statement that the places of the rational function field over an algebraically closed field $K$ are all of degree one, so that they correspond to the points of $\mathbb{P}^1(K)$ and evaluation at a place takes values in $K$. It is used to deduce that every place of $K(t)$ is rational and, through that, in the proof of Weil reciprocity for the rational function field and its algebraically closed special case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_isAlgClosed.lean

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

theorem AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] (v : Place K (RatFunc K)) : v.deg = 1 := by sorry
