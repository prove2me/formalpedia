-- Prove2me | Theorems.Thm_Disjunctive_ExtendedFormulations_pms_polytope_bipartite
-- name    : Disjunctive.ExtendedFormulations.pms_polytope_bipartite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:32:51.733349+00:00
-- url     : https://prove2.me/theorems/b8c36ff3-865e-4ea6-bee6-de2e3b5d6996
-- title:
--   Theorem 5.1 — the PMS polytope of a bipartite graph
-- statement:
--   This is Theorem 5.1 of Balas's *Disjunctive Programming*, the goal theorem of this mission
--   and the one result of the chapter whose full proof the book gives: a linear characterization of
--   the PMS polytope of a bipartite graph, obtained by lifting to edge variables and projecting back.
--
--   Let $G = (V,E)$ be bipartite with bipartition $V = V_1 \cup V_2$. The PMS polytope of $G$ is
--   defined by the system
--
--   $$
--   0 \le x_i \le 1\ (i \in V), \qquad x(V_1) - x(V_2) = 0, \qquad x(S) - x(N(S)) \le 0\ \ (S
--   \subseteq V_1).
--   $$
--
--   If the box constraint $0 \le x_i \le 1$ is replaced by $x_i \in \{0,1\}$, this is simply the
--   König–Hall condition restated in incidence-vector form; the theorem's actual content is that the
--   *fractional* relaxation of this system is already integral, i.e. equals the PMS polytope exactly.
--   The proof lifts to edge variables $u_{ij}$ whose coefficient matrix is totally unimodular
--   (so the lifted polyhedron is automatically integral), then projects back down using Chapter 2's
--   projection machinery.
--
--   **Formalization Note.** The bipartition is recorded as `part : V → Bool` with `hBip` asserting
--   adjacent vertices get different values, rather than two separate `Set V` halves — this keeps
--   membership in each side decidable, needed for the `Finset` sums `x(V_1)`, `x(V_2)`.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 74, Theorem 5.1

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.1 (Balas §5.2.1, p. 74, [34]): the PMS polytope of a bipartite graph `G` with
bipartition recorded by `part : V → Bool` is defined by the system (5.5). -/
theorem pms_polytope_bipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (part : V → Bool) (hBip : ∀ i j, G.Adj i j → part i ≠ part j) :
    PMSPolytope G =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        xSum x (Finset.univ.filter (fun i => part i = true)) =
          xSum x (Finset.univ.filter (fun i => part i = false)) ∧
        ∀ S : Finset V, S ⊆ Finset.univ.filter (fun i => part i = true) →
          xSum x S ≤ xSum x (NeighborsF G S)} := by sorry

end Disjunctive.ExtendedFormulations
