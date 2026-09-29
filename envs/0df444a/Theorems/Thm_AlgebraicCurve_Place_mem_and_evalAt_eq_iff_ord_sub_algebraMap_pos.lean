-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
-- name    : AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/07302f52-3e47-5a8d-a240-d9a5c56a6b55
-- title:
--   Value a at a rational place versus ordᵥ(f-a)>0
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$ in the sense of the project, i.e. a valuation subring $\mathcal O_v =$ `v.toValuationSubring` of $F$ which contains $\operatorname{algebraMap} K F (a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning that the structure map $K \to \mathcal O_v / \mathfrak m_v$ into the residue field of the local ring $\mathcal O_v$ is surjective. Let $f \in F$ and $a \in K$ with $f \neq \operatorname{algebraMap} K F (a)$. Then the conjunction of $f \in \mathcal O_v$ and $\operatorname{evalAt}_v(f) = a$ is equivalent to $0 < \operatorname{ord}_v(f - \operatorname{algebraMap} K F(a))$. Here $\operatorname{evalAt}_v(f)$ is defined to be the image of the residue class of $f$ under a chosen left inverse of $K \to \mathcal O_v / \mathfrak m_v$ when $f \in \mathcal O_v$, and $0$ otherwise, while $\operatorname{ord}_v(g) = -\log$ of the value of $g$ under the valuation attached to the height-one prime of $\mathcal O_v$, so that $\operatorname{ord}_v(0) = 0$; the hypothesis $f \neq \operatorname{algebraMap} K F(a)$ rules out this convention.
--
--   This is the standard dictionary between the value of a function at a rational place and the order of vanishing of $f - a$ at that place. It is used throughout the treatment of places on curves in this development, for instance in the comparison of residues and evaluations on annuli and in the construction of linearly independent families of functions in Riemann–Roch spaces for semistable coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (hv : v.IsRational) (f : F) (a : K) (hfa : f ≠ algebraMap K F a) :
    (f ∈ v.toValuationSubring ∧ v.evalAt f = a) ↔ 0 < v.ord (f - algebraMap K F a) := by sorry
