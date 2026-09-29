-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
-- name    : AlgebraicCurve.Place.isRational_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e4c82b93-d311-5480-b6bd-5d53a5bfc0a1
-- title:
--   Places of a function field over an algebraically closed constant field are rational
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field carrying both a $K$-algebra structure and a $\mathrm{RatFunc}\,K$-algebra structure, compatible in the sense that $K \to \mathrm{RatFunc}\,K \to F$ is a scalar tower, and such that $F$ is finite-dimensional as a $\mathrm{RatFunc}\,K$-vector space; thus $F$ is a finite extension of the rational function field $K(t)$ with $K$ as constant field. Let $v$ be a place of $F$ over $K$, that is, the data of a valuation subring $\mathcal{O}_v = v.\mathtt{toValuationSubring}$ of $F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. The assertion is that $v$ is rational in the sense of the project predicate `IsRational`: the structure map from $K$ to the residue field of the local ring $\mathcal{O}_v$ is surjective, i.e. every residue class is represented by a constant, so the residue field of $v$ is exhausted by $K$.
--
--   This is the classical fact that over an algebraically closed constant field every place of a function field has degree one; it makes all rationality-of-support hypotheses in the theory of evaluation of functions at places and of Weil reciprocity automatic in the geometric setting. It is used throughout the divisor-theoretic and Weil-pairing parts of the development, for instance by [`AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction`](thm.html#AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction) and by the injectivity statements for the divisorial Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.isRational_of_isAlgClosed {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] (v : Place K F) : v.IsRational := by sorry
