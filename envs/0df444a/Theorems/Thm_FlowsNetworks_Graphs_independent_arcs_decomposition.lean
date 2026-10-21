-- Prove2me | Theorems.Thm_FlowsNetworks_Graphs_independent_arcs_decomposition
-- name    : FlowsNetworks.Graphs.independent_arcs_decomposition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:41.730986+00:00
-- url     : https://prove2.me/theorems/c1bce789-f978-47fe-9cba-0d6b20d27403
-- title:
--   Chapter II, Lemma 8.1 — independent sets of arcs give chain decompositions
-- statement:
--   Let $P = \{1, \dots, n\}$ be partially ordered by $\succ$ (irreflexive and transitive), and let $G = [S, T; \mathcal A]$ be the bipartite graph with nodes $x_1, \dots, x_n$, $y_1, \dots, y_n$ and arcs $(x_i, y_j)$ for $i \succ j$.
--
--   Corresponding to any **independent** set $\mathcal J \subseteq \mathcal A$ (pairwise node disjoint arcs) there is a **decomposition** $\Delta$ of $P$ (a partition of $P$ into chains $i_1 \succ i_2 \succ \cdots \succ i_k$) with
--   $$|\mathcal J| + |\Delta| = n.$$
--
--   Together with Lemma 8.2 and the König–Egerváry theorem it yields Dilworth's chain decomposition theorem.
--
--   **Formalization Note** $P$ is `Fin n`, $\succ$ a relation `r` with `IsStrictOrder`; an arc $(x_i, y_j)$ is the index pair $(i, j)$, and independence says every pair in $\mathcal J$ satisfies $i \succ j$ and two distinct pairs differ in both coordinates. $|\Delta|$ is the number of parts of a `Finpartition` of `Fin n` all of whose parts are chains.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 46, Lemma 8.1

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_PosetGraph

namespace FlowsNetworks.Graphs

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Lemma 8.1 (p. 46). Let `P = {1, …, n}` be
partially ordered by `≻` (`r`, a strict partial order) and let `G = [S, T; 𝒜]` be the bipartite
graph with `(x_i, y_j) ∈ 𝒜` iff `i ≻ j`. Corresponding to any independent set `𝒥 ⊆ 𝒜` there is a
decomposition `Δ` of `P` with `|𝒥| + |Δ| = n`. -/
theorem independent_arcs_decomposition {n : ℕ} (r : Fin n → Fin n → Prop) [IsStrictOrder (Fin n) r]
    (J : Finset (Fin n × Fin n)) (hJ : IsIndependentArcs r J) :
    ∃ Δ : Finpartition (Finset.univ : Finset (Fin n)),
      IsDecomposition r Δ ∧ J.card + Δ.parts.card = n := by sorry

end FlowsNetworks.Graphs
