-- Prove2me | Theorems.Thm_Disjunctive_ExtendedFormulations_path_decomposable_subgraph_polytope_v2
-- name    : Disjunctive.ExtendedFormulations.path_decomposable_subgraph_polytope_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:33.662573+00:00
-- url     : https://prove2.me/theorems/14d21512-aaff-4dde-9010-e5068727641c
-- title:
--   Theorem 5.3 — the $s$-$t$ Path Decomposable Subgraph Polytope of an acyclic digraph
-- statement:
--   This is Theorem 5.3 of Balas's *Disjunctive Programming*. Let $G = (V, A)$ be an acyclic digraph with distinguished nodes $s \ne t$. The $s$-$t$ Path Decomposable Subgraph Polytope is the convex hull of the incidence vectors of the sets $W \subseteq V \setminus \{s,t\}$ such that $G(W \cup \{s,t\})$ admits an $s$-$t$ path decomposition (a family of interior-node-disjoint $s$-$t$ paths covering $W$). For $S \subseteq V$ let $\Gamma(S)$ be the out-neighbourhood of $S$ and
--
--   $$\Gamma^*(S) = \begin{cases} (\Gamma(S) \setminus \{t\}) \cup \Gamma(s) & \text{if } t \in \Gamma(S),\\ \Gamma(S) & \text{if } t \notin \Gamma(S).\end{cases}$$
--
--   Then the polytope is defined by the system
--
--   $$0 \le x_i \le 1\ (i \in V), \qquad x(S \setminus \Gamma^*(S)) - x(\Gamma^*(S) \setminus S) \le 0 \quad (S \subseteq V \setminus \{s,t\}).$$
--
--   **Formalization Note.** The retired version transcribed $\Gamma^*(S)$ as $(\Gamma(S) \setminus \{t\}) \cup \{s\}$, the node $s$ in place of its out-neighbourhood $\Gamma(s)$; since $x_s = 0$, this cut off every path-decomposable set containing a predecessor of $t$ (e.g. $W = \{1\}$ for the path $s \to 1 \to t$). The definition module `Disjunctive_ExtendedFormulations_Basic_v2` corrects `GammaStar` (everything else unchanged), checked against the same operator in Balas's 2005 survey (Ann. Oper. Res. 140, Theorem 4.4). As before, the polytope lives in the coordinates of $V \setminus \{s,t\}$, so both sides fix $x_s = x_t = 0$; acyclicity is the book's hypothesis on $G$; a path decomposition is encoded by a degree-constrained arc set (`IsPathDecomposable`).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §5.2.3, p. 75-76, Theorem 5.3 (operator Γ* also in Balas, Ann. Oper. Res. 140 (2005) 125-161, Theorem 4.4)

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic_v2

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.3 (Balas, *Disjunctive Programming*, Springer 2018, §5.2.3, p. 75-76, [13]): the
`s`-`t` Path Decomposable Subgraph Polytope of an acyclic digraph `(V,A)` is defined by the
system `0 ≤ x_i ≤ 1`, `x(S \ Γ*(S)) − x(Γ*(S) \ S) ≤ 0`, `S ⊆ V \ {s,t}`, where
`Γ*(S) = (Γ(S) \ {t}) ∪ Γ(s)` if `t ∈ Γ(S)` and `Γ*(S) = Γ(S)` otherwise. The polytope lives in
the coordinates of `V \ {s,t}` (its points are incidence vectors of subsets of `V \ {s,t}`), so
both sides fix `x_s = x_t = 0`.
Corrected: the retired version used `Γ*(S) = (Γ(S) \ {t}) ∪ {s}` (the node `s` instead of its
out-neighbourhood `Γ(s)`), a mistranscription of the book's operator. -/
theorem path_decomposable_subgraph_polytope_v2 {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) [DecidableRel A] (s t : V) (hst : s ≠ t)
    (hacyclic : IsAcyclicDigraph A) :
    PathDecomposableSubgraphPolytope A s t =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ x s = 0 ∧ x t = 0 ∧
        ∀ S : Finset V, s ∉ S → t ∉ S →
          xSum x (S \ GammaStar A s t S) - xSum x (GammaStar A s t S \ S) ≤ 0} := by sorry

end Disjunctive.ExtendedFormulations
