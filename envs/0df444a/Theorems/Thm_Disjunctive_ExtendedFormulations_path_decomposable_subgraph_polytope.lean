-- Prove2me | Theorems.Thm_Disjunctive_ExtendedFormulations_path_decomposable_subgraph_polytope
-- name    : Disjunctive.ExtendedFormulations.path_decomposable_subgraph_polytope
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:33:55.915883+00:00
-- url     : https://prove2.me/theorems/3feb0aa7-51f8-474a-b354-46bb31d3a486
-- title:
--   Theorem 5.3 — the s-t Path Decomposable Subgraph Polytope
-- statement:
--   This is Theorem 5.3 of Balas's *Disjunctive Programming*, a further analogue of Theorem 5.1
--   for path decompositions of an acyclic digraph.
--
--   For an acyclic digraph $G = (V,A)$ with distinguished nodes $s,t$, the $s$-$t$ Path Decomposable
--   Subgraph Polytope (convex hull of incidence vectors of $W \subseteq V \setminus \{s,t\}$ such
--   that $G(W \cup \{s,t\})$ admits an $s$-$t$ path decomposition) is defined by
--
--   $$
--   0 \le x_i \le 1\ (i \in V), \qquad x(S \setminus \Gamma^*(S)) - x(\Gamma^*(S) \setminus S)
--   \le 0 \quad (S \subseteq V \setminus \{s,t\}),
--   $$
--
--   where $\Gamma^*(S)$ is $\Gamma(S)$ with $t$ replaced by $s$ whenever $t \in \Gamma(S)$ — folding
--   path-endings at $t$ back to the common source $s$ so the same "out-neighborhood exchange"
--   inequality template as Theorem 5.2 applies.
--
--   **Formalization Note.** `IsPathDecomposable` (companion definition) is the degree-constrained arc
--   encoding of "admits a path decomposition"; `GammaStar` implements the $t \to s$ folding exactly
--   as displayed.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 75, Theorem 5.3

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.3 (Balas §5.2.3, p. 75-76, [13]): the `s`-`t` Path Decomposable Subgraph Polytope
of an acyclic digraph `(V,A)` is defined by the system `0 ≤ x_i ≤ 1`, `x(S \ Γ*(S)) − x(Γ*(S) \
S) ≤ 0`, `S ⊆ V \ {s,t}`. The polytope's points are incidence vectors of subsets of `V \ {s,t}`,
so both sides fix `x_s = x_t = 0`; without that the unit vector `e_s` satisfies the system and is
not in the polytope. Acyclicity is the page's own hypothesis on the digraph. -/
theorem path_decomposable_subgraph_polytope {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) [DecidableRel A] (s t : V) (hst : s ≠ t)
    (hacyclic : IsAcyclicDigraph A) :
    PathDecomposableSubgraphPolytope A s t =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x s = 0 ∧ x t = 0 ∧
        ∀ S : Finset V, s ∉ S → t ∉ S →
          xSum x (S \ GammaStar A s t S) - xSum x (GammaStar A s t S \ S) ≤ 0} := by sorry

end Disjunctive.ExtendedFormulations
