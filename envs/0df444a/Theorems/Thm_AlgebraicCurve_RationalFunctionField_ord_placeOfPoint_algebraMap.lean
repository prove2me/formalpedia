-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
-- name    : AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/1a43d932-e0c1-5826-a18d-35cc3cba5bd9
-- title:
--   Order at the place t=a equals root multiplicity
-- statement:
--   Let $K$ be a field, let $a \in K$, and let $q \in K[X]$ be a nonzero polynomial. Consider the place `placeOfPoint K a` of the rational function field $K(X)$ attached to the point $X = a$: it is the place obtained from the height-one prime $(X-a)$ of $K[X]$ — the data of a valuation subring of $K(X)$ containing the image of $K$, distinct from all of $K(X)$ and a principal ideal ring — namely the local ring of $K(X)$ at $X-a$. For a place $v$, $v.\mathrm{ord}$ of an element $f$ is defined as $-\log$ of the value of $f$ under the $\mathbb{Z}^{m0}$-valued adic valuation associated with the corresponding height-one prime. The assertion is that the order of the image of $q$ under the map $K[X] \to K(X)$ at this place equals `Polynomial.rootMultiplicity a q`, the largest $m$ with $(X-a)^m \mid q$.
--
--   This is the basic dictionary, for the rational function field, between the order of vanishing of a rational function at the place corresponding to a rational point $a$ of $\mathbb{P}^1$ and the multiplicity of $a$ as a root of a polynomial. It is used throughout the development of places and divisors of $K(X)$, for instance in computing orders of differences of coordinates and ramification indices along maps of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap.lean

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

theorem AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap {K : Type*} [Field K] (a : K) {q : Polynomial K} (hq : q ≠ 0) : (placeOfPoint K a).ord (algebraMap (Polynomial K) (RatFunc K) q) = Polynomial.rootMultiplicity a q := by sorry
