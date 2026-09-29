-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
-- name    : AlgebraicCurve.RationalFunctionField.deg_placeInfty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/7dae8346-786a-5cde-b729-973c2fb2060b
-- title:
--   The place at infinity of K(t) has degree one
-- statement:
--   Let $K$ be a field. Consider the rational function field $\mathrm{RatFunc}\,K$ and the place $\mathtt{placeInfty}\ K$ of $\mathrm{RatFunc}\,K$ over $K$, that is, the datum consisting of the valuation subring attached to the infinity valuation `RatFunc.inftyValuation K` of $\mathrm{RatFunc}\,K$, together with the verifications required by the structure `Place`: that every element $\mathrm{algebraMap}\,K\,(\mathrm{RatFunc}\,K)(a)$, $a \in K$, lies in this subring (the infinity valuation is trivial on the constants), that the subring is not all of $\mathrm{RatFunc}\,K$, and that it is a principal ideal ring (being a discrete valuation ring). The degree of a place $v$ is by definition $\mathrm{Module.finrank}$ over $K$ of its residue field, the residue field of the local ring $v.\mathtt{toValuationSubring}$. The assertion is that $(\mathtt{placeInfty}\ K).\deg = 1$, i.e. the residue field of the infinity valuation ring of $K(t)$ is one-dimensional as a $K$-vector space, so that the place at infinity is a rational place. No hypothesis on $K$ beyond being a field is imposed.
--
--   This is the classical fact that, among the places of the rational function field $K(t)$ — the monic irreducible polynomials together with $\infty$ — the place at infinity is rational, its residue field being $K$ itself. It identifies the named place at infinity as a degree-one point of $\mathbb{P}^1$ and is used throughout the function-field foundations, for instance in the Riemann–Roch-style computations for $K(t)$ such as [`AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero`](thm.html#AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero) and the finite-dimensionality of the space attached to the zero divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty.lean

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

theorem AlgebraicCurve.RationalFunctionField.deg_placeInfty (K : Type*) [Field K] [DecidableEq (RatFunc K)] : (placeInfty K).deg = 1 := by sorry
