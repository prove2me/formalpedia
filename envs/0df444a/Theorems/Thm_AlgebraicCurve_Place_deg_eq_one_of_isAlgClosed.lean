-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
-- name    : AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/30b3cd0c-85fb-53b0-8fd2-3ee7661282e8
-- title:
--   Places over an algebraically closed field have degree one
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose $K$ is algebraically closed. Let $v$ be a place of $F$ over $K$ in the sense of the project, that is, a valuation subring $\mathcal{O}_v \subseteq F$ which contains the image of $K$ under the structure map $K \to F$, is not all of $F$, and is a principal ideal ring. Write $\kappa(v) = \mathcal{O}_v / \mathfrak{m}_v$ for its residue field, a $K$-algebra, and let $v.\mathrm{deg}$ be the $K$-dimension $\operatorname{finrank}_K \kappa(v)$, which by Mathlib's convention is $0$ both when $\kappa(v)$ is the zero module and when it is infinite-dimensional over $K$. Assume $v.\mathrm{deg} \neq 0$, i.e. $\kappa(v)$ is a nonzero finite-dimensional $K$-vector space. The conclusion is that $v.\mathrm{deg} = 1$, i.e. the structure map $K \to \kappa(v)$ is an isomorphism. No hypothesis that $F$ is a function field over $K$, nor any finiteness or transcendence-degree condition on $F/K$, enters; the only finiteness used is the one encoded in $v.\mathrm{deg} \neq 0$.
--
--   This is the standard remark that over an algebraically closed constant field every place of residue degree defined (i.e. with finite-dimensional residue field) has degree one, so that degrees of divisors over $\bar{K}$ are just counts of points. It is used throughout the divisor and divisor-class machinery for curves, for instance in the comparison of places under a finite extension and in the ramification estimates for Galois covers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by sorry
