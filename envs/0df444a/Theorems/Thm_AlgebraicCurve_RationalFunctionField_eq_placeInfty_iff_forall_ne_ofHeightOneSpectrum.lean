-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
-- name    : AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/5dc01e2e-6b78-580e-ae5e-511e2495ea8f
-- title:
--   The infinite place of K(t) characterised among all places
-- statement:
--   Let $K$ be a field. Work with the type `Place K (RatFunc K)` of places of the rational function field $K(t)$ over $K$, an element of which consists of a valuation subring of $K(t)$ that contains $\mathrm{algebraMap}\,K\,K(t)(a)$ for every $a \in K$, is not all of $K(t)$, and is a principal ideal ring. For such a $v$, the theorem asserts the equivalence: $v$ equals `placeInfty K`, the place whose valuation subring is the valuation subring of the degree-at-infinity valuation `RatFunc.inftyValuation K` of $K(t)$, if and only if for every height-one prime $w$ of the polynomial ring $K[X]$ one has $v \neq$ `Place.ofHeightOneSpectrum w`, the latter being the place whose valuation subring is that of the $w$-adic valuation of $K(t)$ attached to $w$ by the Dedekind domain $K[X]$. Thus the place at infinity is exactly the place of $K(t)/K$ which is not the $w$-adic place of any nonzero prime of $K[X]$.
--
--   This is the classical description of the places of the rational function field: they are the $P$-adic places for $P$ a monic irreducible polynomial together with the single place at infinity; here that description is packaged as an intrinsic characterisation of `placeInfty K`, so that the infinite place can be recognised by a property not mentioning its construction. It is used to split the places of $K(t)$ into the finite ones and the one at infinity, and in the treatment of places on modular curves via prolongation pairs and chart data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum.lean

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

theorem AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : v = placeInfty K ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by sorry
