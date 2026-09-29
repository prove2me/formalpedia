-- Prove2me | Theorems.Thm_ChvatalPolytopes_Perfect_clique_system_defines_iff_perfect
-- name    : ChvatalPolytopes.Perfect.clique_system_defines_iff_perfect
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:15:57.740966+00:00
-- url     : https://prove2.me/theorems/54b7f733-a3e5-429d-b41c-5bf05341ee3b
-- title:
--   Theorem 3.1 — the clique inequalities define $P(G)$ if and only if $G$ is perfect
-- statement:
--   Let $G=(V,E)$ be a finite graph, $P(G)$ the convex hull of the incidence vectors of its stable sets, and $C(G)$ the vertex sets of its maximal cliques. The following two conditions are equivalent:
--
--   1. the inequalities
--   $$-x_u\le0\quad(u\in V),\qquad \sum_{u\in W}x_u\le1\quad(W\in C(G))$$
--   constitute a defining linear system of $P(G)$, i.e. a vector $x\in\mathbb R^V$ satisfies all of them if and only if $x\in P(G)$;
--   2. $G$ is perfect (in the $\alpha$-perfect sense: for every zero–one $c$, the maximum weight of a stable set equals the minimum number of maximal cliques covering the support of $c$).
--
--   Thus the nonnegativity and clique inequalities — which are valid for $P(G)$ for every graph — describe the stable set polytope completely exactly for perfect graphs. Combined with the perfect graph theorem this gives a polyhedral characterization of perfect graphs.
--
--   **Formalization Note** "Defining linear system" is the equality of sets between the solution set of the displayed system and $P(G)=\operatorname{conv}S(G)$. The clique inequalities range over the **maximal** cliques, as on the page. Perfection is the mission's `IsPerfect`, the paper's own zero–one min–max, not Berge's $\chi=\omega$ definition.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 140, Theorem 3.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Theorem 3.1** (Chvátal 1975, p. 140). For every graph `G = (V, E)`, the following two
conditions are equivalent:
(i) the inequalities `−x_u ≤ 0 (u ∈ V)` and `Σ (x_u : u ∈ W) ≤ 1 (W ∈ C(G))` constitute a
defining linear system of `P(G)`, i.e. their solution set is exactly `P(G) = conv S(G)`;
(ii) `G` is perfect (the paper's α-perfection, `IsPerfect`).
`C(G)` is the set of vertex sets of the **maximal** cliques of `G`. -/
theorem clique_system_defines_iff_perfect {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} = stablePolytope G ↔
      IsPerfect G := by sorry

end ChvatalPolytopes.Perfect
