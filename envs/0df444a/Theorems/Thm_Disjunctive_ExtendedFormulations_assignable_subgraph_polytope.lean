-- Prove2me | Theorems.Thm_Disjunctive_ExtendedFormulations_assignable_subgraph_polytope
-- name    : Disjunctive.ExtendedFormulations.assignable_subgraph_polytope
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:33:19.68974+00:00
-- url     : https://prove2.me/theorems/cd94d556-3e20-4268-a7e1-2bfeb7b5d6df
-- title:
--   Theorem 5.2 — the Assignable Subgraph Polytope of a digraph
-- statement:
--   This is Theorem 5.2 of Balas's *Disjunctive Programming*, the digraph analogue of Theorem
--   5.1: the Assignment Problem's natural extension to subsets that admit a cycle decomposition.
--
--   For a digraph $G = (V,A)$, the Assignable Subgraph Polytope (the convex hull of incidence vectors
--   of vertex sets $W$ such that $G(W)$ admits a cycle decomposition) is defined by
--
--   $$
--   0 \le x_i \le 1\ (i \in V), \qquad x(S \setminus \Gamma(S)) - x(\Gamma(S) \setminus S) \le
--   0 \quad (S \subseteq V),
--   $$
--
--   where $\Gamma(S)$ is the out-neighborhood of $S$. As with Theorem 5.1, projection is used to
--   prove this fractional system already describes an integral polytope, without needing to verify a
--   totally-unimodular lift by hand for every instance.
--
--   **Formalization Note.** `A : V → V → Prop` is a general digraph relation (not required
--   irreflexive or asymmetric, matching the book's unrestricted notion of a digraph); `IsAssignable`
--   uses `Equiv.Perm` on the subtype `{v // v ∈ W}`, since any permutation of a finite set decomposes
--   into disjoint cycles by definition.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 75, Theorem 5.2

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.2 (Balas §5.2.2, p. 75, [13]): the Assignable Subgraph Polytope of a digraph `G`
is defined by the system `0 ≤ x_i ≤ 1`, `x(S \ Γ(S)) − x(Γ(S) \ S) ≤ 0`, `S ⊆ V`. -/
theorem assignable_subgraph_polytope {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    [DecidableRel A] :
    AssignableSubgraphPolytope A =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ S : Finset V, xSum x (S \ GammaOut A S) - xSum x (GammaOut A S \ S) ≤ 0} := by sorry

end Disjunctive.ExtendedFormulations
