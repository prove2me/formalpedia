-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_convex_hull_disjunctive_set
-- name    : Disjunctive.ConvexHull.convex_hull_disjunctive_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:10:30.853854+00:00
-- url     : https://prove2.me/theorems/d6f71797-1031-4cd7-bace-2f9459334ca0
-- title:
--   Theorem 2.1 — the convex hull of a disjunctive set
-- statement:
--   This is Theorem 2.1 of Balas's *Disjunctive Programming*, the book's flagship result and the
--   reason the book is worth formalizing at all: a compact, higher-dimensional description of the
--   closed convex hull of an arbitrary union of finitely many polyhedra.
--
--   Let $Q$ be a finite index set and, for $h \in Q$, let $P_h := \{x \in \mathbb{R}^n : A_h x \ge
--   b_h\}$, forming the disjunctive set $F := \bigcup_{h \in Q} P_h$ and the feasible index set
--   $Q^* := \{h : P_h \ne \emptyset\}$. Then
--
--   $$
--   \mathrm{cl}\,\mathrm{conv}(F) \;=\; \Big\{ x \in \mathbb{R}^n : \exists\, (y^h, y^h_0) \in
--   \mathbb{R}^{n+1},\ h \in Q^*,\ \text{with } x = \!\!\sum_{h \in Q^*}\!\! y^h,\ A_h y^h - b_h
--   y^h_0 \ge 0,\ y^h_0 \ge 0\ (h \in Q^*),\ \!\!\sum_{h \in Q^*}\!\! y^h_0 = 1 \Big\}.
--   $$
--
--   That is, the closed convex hull of a union of $q := |Q|$ polyhedra in $\mathbb{R}^n$ is itself
--   the projection of a *single* polyhedron living in the much larger space $\mathbb{R}^n \times
--   (\mathbb{R}^n)^{Q^*} \times \mathbb{R}^{Q^*}$, whose dimension grows only *linearly* in $q$ and
--   $n$ (in fact $n + (n+1)|Q^*| - 1$ after eliminating one redundant $y^h_0$), even though the
--   convex hull of a union of polyhedra generally has exponentially many facets when described
--   directly in $\mathbb{R}^n$.
--
--   **Formalization Note.** `DisjunctiveSet`, `FeasibleIndices`, `LiftedPolyhedron`, and `ProjX`
--   are the companion definitions. `closure (convexHull ℝ ·)` is Mathlib's closed convex hull;
--   the theorem is genuinely about the *closed* hull (Balas's Remark right after the proof notes
--   when the closure is redundant, e.g. when $F$ is a union of polytopes).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 19, Theorem 2.1

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Theorem 2.1 (Balas §2.1, p. 19, [6]): the closed convex hull of a disjunctive set
`F = ⋃_{h∈Q} P_h` equals the projection onto `x` of the lifted polyhedron `(2.1)` over `Q*`. -/
theorem convex_hull_disjunctive_set {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    closure (convexHull ℝ (DisjunctiveSet m A b)) =
      ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) := by sorry

end Disjunctive.ConvexHull
