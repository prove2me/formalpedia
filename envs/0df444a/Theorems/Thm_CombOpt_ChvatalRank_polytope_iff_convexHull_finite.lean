-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_polytope_iff_convexHull_finite
-- name    : CombOpt.ChvatalRank.polytope_iff_convexHull_finite
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:35.024927+00:00
-- url     : https://prove2.me/theorems/151c9621-17d7-40b0-9839-5cceac6bf3f8
-- title:
--   Theorem 6.11 — a set is a polytope iff it is the convex hull of a finite set
-- statement:
--   A set $P\subseteq\mathbb R^n$ is a polytope if and only if there exists a finite set $V\subseteq\mathbb R^n$ such that
--   $$
--   P=\operatorname{conv}(V).
--   $$
--   This is the bridge between the description of a polytope by inequalities and by points. In this mission it shows that $P_I$ is a polytope when $P$ is, since a polytope has finitely many integral vectors.
--
--   **Formalization Note** $V=\emptyset$ gives the empty polytope.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.11, p. 206 (PDF 214)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsPolytope

open Matrix

namespace CombOpt.ChvatalRank

/-- **Theorem 6.11.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.11, p. 206 (PDF 214): "A set P is a polytope if and only if there
exists a finite set V such that P is the convex hull of V."

**Formalization Note.** `P ⊆ ℝⁿ` for a fixed `n`, as in the book. `V = ∅` gives the empty polytope. -/
theorem polytope_iff_convexHull_finite {n : ℕ} (P : Set (Fin n → ℝ)) :
    IsPolytope P ↔ ∃ V : Set (Fin n → ℝ), V.Finite ∧ P = convexHull ℝ V := by sorry

end CombOpt.ChvatalRank
