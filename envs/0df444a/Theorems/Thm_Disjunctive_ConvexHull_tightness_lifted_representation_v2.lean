-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_tightness_lifted_representation_v2
-- name    : Disjunctive.ConvexHull.tightness_lifted_representation_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:40.792275+00:00
-- url     : https://prove2.me/theorems/c14c7d9d-f7e9-482c-8bfd-a56fdbe67f31
-- title:
--   Theorem 2.3 — when the lifting may be indexed by all of $Q$
-- statement:
--   This is Theorem 2.3 of Balas's *Disjunctive Programming*: when the lifted representation of Theorem 2.1 may be indexed by all of $Q$ instead of the (a priori unknown) set $Q^*$ of nonempty disjuncts.
--
--   Let $P_h := \{x : A_h x \ge b_h\}$ ($h \in Q$), $F := \bigcup_h P_h$, $Q^* := \{h : P_h \ne \emptyset\}$, and $C_h := \{y : A_h y \ge 0\}$. Let $P$ be the projection onto $x$ of the lifted system (2.1) over $Q^*$ (so $P = \mathrm{cl\,conv}\,F$ by Theorem 2.1) and $P_Q$ the projection of the same system written over all of $Q$. Assume $F \ne \emptyset$. Then
--   $$
--   P_Q = P \iff C_k \subseteq \sum_{h \in Q^*} C_h \quad \text{for every } k \in Q \setminus Q^* .
--   $$
--
--   **Formalization Note.** The retired version omitted the book's assumption $F \neq \emptyset$; when every disjunct is empty, both projections are empty while $\sum_{h\in\emptyset} C_h = \{0\}$, so an empty disjunct with a nonzero recession cone (e.g. $0\cdot x \ge 1$) refuted it. The new statement adds `hF : F.Nonempty` (equivalently $Q^* \ne \emptyset$). As before, $P_Q = P$ is read as equality of the $x$-projections, which is the identity $P_Q = P + \sum_{k \notin Q^*} C_k$ the book's proof establishes; the lifted vectors are padded by zeros outside the index set (mission convention).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §2.1, p. 22, Theorem 2.3

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Theorem 2.3 (Balas, *Disjunctive Programming*, Springer 2018, §2.1, p. 22): assume `F ≠ ∅`.
Then `P_Q = P` if and only if every disjunct's recession cone outside `Q*` is contained in the
Minkowski sum of the recession cones inside `Q*`. `P` is the `x`-set of Theorem 2.1 (the
projection of the lifted polyhedron over `Q*`) and `P_Q` the same projection with `Q` in place
of `Q*`; the book's proof computes `P_Q = P + Σ_{k ∉ Q*} C_k`, an identity in `x`-space.

Version 2: adds the book's assumption `F ≠ ∅` (equivalently `Q* ≠ ∅`). Without it, `Q* = ∅`
makes both projections empty while the Minkowski sum over `∅` is `{0}`, so an empty disjunct with
a nonzero recession cone (e.g. `0·x ≥ 1`) refuted the retired statement. -/
theorem tightness_lifted_representation_v2 {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ)
    (hF : (DisjunctiveSet m A b).Nonempty) :
    ProjX (LiftedPolyhedron m A b Set.univ) = ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) ↔
      ∀ k, k ∉ FeasibleIndices m A b →
        RecessionCone (A k) ⊆ MinkowskiSumOver (FeasibleIndices m A b) (fun h => RecessionCone (A h)) := by sorry

end Disjunctive.ConvexHull
