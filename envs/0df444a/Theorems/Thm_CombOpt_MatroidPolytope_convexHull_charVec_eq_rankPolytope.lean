-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_convexHull_charVec_eq_rankPolytope
-- name    : CombOpt.MatroidPolytope.convexHull_charVec_eq_rankPolytope
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:23.680931+00:00
-- url     : https://prove2.me/theorems/ed007130-a9cb-4ce2-8fb4-33a4a8a377e1
-- title:
--   Theorem 8.5 — Edmonds' Matroid Polytope Theorem
-- statement:
--   Let $(S,\mathcal I)$ be a matroid on a finite set $S$ with rank function $r$. Then the convex hull of the characteristic vectors of the independent sets is
--   $$\operatorname{conv}\{\chi^J : J\in\mathcal I\}=\{x\in\mathbb R^S : x\ge 0,\ x(A)\le r(A)\ \text{for all } A\subseteq S\},$$
--   where $x(A)=\sum_{e\in A}x_e$.
--
--   The theorem (Edmonds 1970) gives a complete linear description of the matroid polytope, so that maximum-weight independent set problems are linear programs over an explicit system; it is the model for the matroid intersection polytope and many later polyhedral results.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.5, p. 279 (PDF p. 286)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_rankPolytope
import Definitions.Def_OnlineCRS_Combine_indicatorVec

namespace CombOpt.MatroidPolytope

/-- **Theorem 8.5: Edmonds' Matroid Polytope Theorem.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 8.5, p. 279 (PDF p. 286): "Let (S, I) be a matroid with rank function r. The convex
hull of characteristic vectors of independent sets is {x ∈ R^S : x ≥ 0, x(A) ≤ r(A) for all
A ⊆ S}."

For a matroid `I` on a finite ground set `α`, the convex hull in `ℝ^α` of the characteristic
vectors of the independent sets equals `rankPolytope I`.

**Formalization Note.** The characteristic vector of `J` is the published
`OnlineCRS.Combine.indicatorVec J` (`1` on `J`, `0` off `J`). -/
theorem convexHull_charVec_eq_rankPolytope {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α → Prop) (hI : IsMatroid I) :
    convexHull ℝ {x : α → ℝ | ∃ J : Finset α, I J ∧ x = OnlineCRS.Combine.indicatorVec J} =
      rankPolytope I := by sorry

end CombOpt.MatroidPolytope
