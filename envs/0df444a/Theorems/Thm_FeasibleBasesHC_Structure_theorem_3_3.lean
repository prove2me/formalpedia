-- Prove2me | Theorems.Thm_FeasibleBasesHC_Structure_theorem_3_3
-- name    : FeasibleBasesHC.Structure.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:09.522993+00:00
-- url     : https://prove2.me/theorems/6f70bf37-4ef7-46e0-b575-800113a30ece
-- title:
--   Theorem 3.3, p. 12 — thick and thin arcs of an ultimate basis
-- statement:
--   Let $(B,L,U)\in\Gamma(G)$ with basic arcs $A$, thick arcs $A_1$ and thin arcs $A_2$. Then all four conclusions hold:
--
--   $$A=A_1\cup A_2;\qquad A_1\text{ is a spanning collection of disjoint directed cycles};\qquad 2|L|\le n-1,\;2|U|\le n-1.$$
--
--   Also, every node other than node $1$ is reachable from node $1$ along arcs in $A_1\cup A_2$. The cycle collection is represented by a permutation of all vertices. This theorem identifies the large-flow matching used in Theorem 3.4.
--
--   **Formalization Note** Paper node $1$ is `0 : Fin n`; `[NeZero n]` ensures it exists. `Relation.TransGen` expresses a nonempty directed path. Multiplying the cardinality bounds by two avoids fractional natural-number division.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, p. 12, Theorem 3.3 (i)–(iv)

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Setting

namespace FeasibleBasesHC.Structure

/-- Theorem 3.3(i)--(iv): no intermediate arcs, a thick cycle cover, reachability,
    and the bounds on lower- and upper-bound nonbasic slacks. -/
theorem theorem_3_3 {n : ℕ} [NeZero n] (G : Digraph n)
    (b : Basis n) (hb : b ∈ GamUlt G) :
    b.A = thickArcs G b ∪ thinArcs G b ∧
    (∃ σ : Equiv.Perm (Fin n),
      thickArcs G b = Finset.univ.image (fun i : Fin n => (i, σ i))) ∧
    (∀ i : Fin n, i ≠ 0 → Relation.TransGen (fun u v : Fin n => (u, v) ∈ b.A) 0 i) ∧
    2 * b.L.card ≤ n - 1 ∧ 2 * b.U.card ≤ n - 1 := by sorry

end FeasibleBasesHC.Structure
