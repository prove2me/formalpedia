-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
-- name    : AlgebraicCurve.Place.isRational_iff_deg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/1af570e5-1c20-5298-9e2d-bff0496b3ec8
-- title:
--   A place is rational iff its degree is 1
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project: a valuation subring $\mathcal{O}_v \subseteq F$ that contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. Write $\kappa(v)$ for the residue field of the local ring $\mathcal{O}_v$, and let $\deg v$ be the $K$-dimension $\operatorname{finrank}_K \kappa(v)$ of $\kappa(v)$ as a $K$-module (which is $0$ by the Mathlib convention when this dimension is infinite). The theorem asserts the equivalence: the structure map $K \to \kappa(v)$ is surjective (the project's notion of $v$ being rational) if and only if $\deg v = 1$. In particular the degree-one condition already forces $\kappa(v)$ to be finite-dimensional over $K$, so no separate finiteness hypothesis occurs.
--
--   This is the standard characterisation of the rational (degree-one) places of a function field $F/K$, as in the basic theory of places and their residue class fields. It belongs to the evaluation-of-functions layer underlying divisors, Weil reciprocity and the divisorial Weil pairing, and is invoked throughout that development whenever rational places are identified with places of degree $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by sorry
