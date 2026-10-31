-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_11
-- name    : CombOpt.MatchingPolytope.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:30.926793+00:00
-- url     : https://prove2.me/theorems/c0debf07-ba51-432d-b139-8f14a40becb0
-- title:
--   Theorem 6.11 — polytopes are exactly convex hulls of finite sets
-- statement:
--   A set $P\subseteq\mathbb R^n$ is a polytope if and only if there exists a finite set $V\subseteq\mathbb R^n$ such that
--   $$P=\operatorname{conv.hull}(V).$$
--
--   This makes it possible to describe the convex hull of any finite combinatorial family by finitely many linear inequalities, the starting point of polyhedral combinatorics.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. $V=\emptyset$ gives $P=\emptyset$, which is a polytope.
--
--   Differences from the source:
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.11, p. 206 (PDF p. 214)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_CombOpt_MatchingPolytope_IsPolytope

namespace CombOpt.MatchingPolytope

/-- **Theorem 6.11** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.11, p. 206 (PDF p. 214):
"A set P is a polytope if and only if there exists a finite set V such that P is the convex hull
of V."

**Formalization Note.** `ℝ^n` is `ι → ℝ` for a finite type `ι`; `convexHull ℝ` is the book's
`conv.hull`. `V = ∅` gives `P = ∅`, which is a polytope. -/
theorem theorem_6_11 {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) :
    IsPolytope P ↔ ∃ V : Set (ι → ℝ), V.Finite ∧ P = convexHull ℝ V := by sorry

end CombOpt.MatchingPolytope
