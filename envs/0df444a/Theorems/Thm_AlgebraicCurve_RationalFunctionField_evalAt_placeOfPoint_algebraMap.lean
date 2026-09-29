-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap
-- name    : AlgebraicCurve.RationalFunctionField.evalAt_placeOfPoint_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/a0cf1c1f-87da-5e6b-a360-29b3eceda9e8
-- title:
--   Evaluation at the place t=a of K(t) is q ↦ q(a)
-- statement:
--   Let $K$ be a field, let $a \in K$, and let $q \in K[X]$ be a polynomial. Consider the place `placeOfPoint K a` of the rational function field $K(X)$ over $K$: it is the place attached, via `Place.ofHeightOneSpectrum`, to the height-one prime of $K[X]$ determined by the irreducible polynomial $X - a$; concretely it is the datum of a valuation subring of $K(X)$ which contains the image of $K$, is not all of $K(X)$, and is a principal ideal ring. For such a place $v$, the evaluation map $v.\mathrm{evalAt} : K(X) \to K$ sends an element $f$ lying in the valuation subring to the preimage under $\mathrm{algebraMap}\ K\ v.\mathrm{ResidueField}$ (taken via `Function.invFun`) of the residue class of $f$, and sends any $f$ outside the valuation subring to $0$. The assertion is that applying this evaluation to the image of $q$ under the inclusion $K[X] \hookrightarrow K(X)$ yields exactly the ordinary value $q(a)$ of the polynomial $q$ at $a$, i.e. `Polynomial.eval a q`.
--
--   This is the dictionary identifying the residue-field evaluation at the place of $K(X)$ associated with the linear polynomial $X - a$ with literal evaluation of polynomials at the rational point $a$, for the place-theoretic description of $\mathbb{P}^1$ over $K$. It is used in the construction of chart data from residues along lines on modular curves, via [`ModularCurve.exists_chartData_of_lineResidues`](thm.html#ModularCurve.exists_chartData_of_lineResidues).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap.lean

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

theorem AlgebraicCurve.RationalFunctionField.evalAt_placeOfPoint_algebraMap {K : Type*} [Field K] (a : K) (q : Polynomial K) : (placeOfPoint K a).evalAt (algebraMap (Polynomial K) (RatFunc K) q) = q.eval a := by sorry
