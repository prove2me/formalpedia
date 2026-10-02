-- Prove2me | Theorems.Thm_Disjunctive_ExtendedFormulations_pms_polytope_general
-- name    : Disjunctive.ExtendedFormulations.pms_polytope_general
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:34:28.120328+00:00
-- url     : https://prove2.me/theorems/770f3833-97a8-4960-9a73-8c5dceedf54a
-- title:
--   Theorem 5.4 — the PMS polytope of an arbitrary graph
-- statement:
--   This is Theorem 5.4 of Balas's *Disjunctive Programming*: the PMS polytope characterization
--   extended from bipartite to arbitrary graphs, at the cost of a more intricate inequality and a
--   side condition on which subsets it applies to. The book outsources its proof to [35], but pins
--   down every hypothesis precisely on the page.
--
--   For an arbitrary graph $G = (V,E)$, with $c(S)$ the number of connected components of $G(S)$, the
--   PMS polytope is defined by
--
--   $$
--   0 \le x_i \le 1\ (i \in V), \qquad x(S) - x(N(S)) \le |S| - c(S)
--   $$
--
--   for every $S \subseteq V$ such that every component of $G(S)$ is either a single node or a
--   nonbipartite graph with an odd number of nodes. Unlike Theorem 5.1's bipartite case (inequality
--   right-hand side always $0$), the general case needs the sharper right-hand side $|S| - c(S)$ and
--   the side condition restricting which $S$ contribute a facet — dropping either would either
--   under-describe or mis-describe the polytope.
--
--   **Formalization Note.** `IsComponentOf`/`IsBipartiteOn`/`ComponentCount` (companion definitions)
--   pin down "component," "nonbipartite," and $c(S)$ directly via reachability and 2-colorability. The
--   side condition is stated as a hypothesis inside the inequality's own universal quantifier over
--   $S$, exactly restricting which $S$ the inequality is asserted for, matching "for all $S$ such
--   that..." precisely.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 76, Theorem 5.4

import Mathlib
import Definitions.Def_Disjunctive_ExtendedFormulations_Basic
import Definitions.Def_Disjunctive_ExtendedFormulations_Components

namespace Disjunctive.ExtendedFormulations

/-- Theorem 5.4 (Balas §5.2.4, p. 76-77, [35]): the PMS polytope of an arbitrary graph `G` is
defined by the system (5.7): `0 ≤ x_i ≤ 1`, and `x(S) − x(N(S)) ≤ |S| − c(S)` for every `S ⊆ V`
all of whose components are either single nodes or nonbipartite with an odd number of nodes. -/
theorem pms_polytope_general {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    PMSPolytope G =
      {x : V → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        ∀ S : Finset V,
          (∀ C : Finset V, IsComponentOf G S C → C.card = 1 ∨ (¬ IsBipartiteOn G C ∧ Odd C.card)) →
            xSum x S - xSum x (NeighborsF G S) ≤ (S.card : ℝ) - (ComponentCount G S : ℝ)} := by sorry

end Disjunctive.ExtendedFormulations
