-- Prove2me | Theorems.Thm_CombOpt_MatchingPolytope_theorem_6_10
-- name    : CombOpt.MatchingPolytope.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:11.86713+00:00
-- url     : https://prove2.me/theorems/57a88625-4bd8-4385-98f8-f473f491b54a
-- title:
--   Theorem 6.10 — a polytope is the convex hull of its (finitely many) vertices
-- statement:
--   Let $P\subseteq\mathbb R^n$ be a polytope. Then $P$ has finitely many vertices and
--   $$P=\operatorname{conv.hull}\{v:\ v \text{ a vertex of } P\}.$$
--
--   Together with Theorem 6.11 this is the equivalence between the "external" description of a polytope by inequalities and the "internal" one by finitely many points.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product.
--
--   Differences from the source:
--   - reading: "the convex hull of its vertices", with conv.hull defined for finite sets (p. 199) → the vertex set is finite, and $P$ is its convex hull; reason: the printed statement presupposes that the vertex set is finite; the Lean statement asserts it
--   - encoding: vectors in $\mathbb R^n$ → functions $\iota\to\mathbb R$ on a finite type $\iota$; reason: every finite $\iota$ is $\{1,\dots,n\}$ up to relabelling; $\iota=\mathrm{Fin}\,n$ is the book's $\mathbb R^n$
--   - encoding: conv.hull$(S)$ of a finite set, the set of convex combinations of $S$ (p. 199) → Mathlib's `convexHull ℝ S`; reason: for a finite set both are the set of convex combinations of finitely many points of $S$
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.10, p. 206 (PDF p. 214)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_CombOpt_MatchingPolytope_IsPolytope
import Definitions.Def_CombOpt_MatchingPolytope_IsValid
import Definitions.Def_CombOpt_MatchingPolytope_IsSupportingHyperplane
import Definitions.Def_CombOpt_MatchingPolytope_IsFace
import Definitions.Def_CombOpt_MatchingPolytope_IsVertex

namespace CombOpt.MatchingPolytope

/-- **Theorem 6.10** — Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.10, p. 206 (PDF p. 214):
"A polytope is equal to the convex hull of its vertices."

**Formalization Note.** The book's `conv.hull` is defined for finite sets (p. 199), so the
statement presupposes that a polytope has finitely many vertices; the Lean statement asserts this
finiteness together with the equality. `convexHull ℝ` is the set of convex combinations. -/
theorem theorem_6_10 {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (hP : IsPolytope P) :
    {v | IsVertex P v}.Finite ∧ P = convexHull ℝ {v | IsVertex P v} := by sorry

end CombOpt.MatchingPolytope
