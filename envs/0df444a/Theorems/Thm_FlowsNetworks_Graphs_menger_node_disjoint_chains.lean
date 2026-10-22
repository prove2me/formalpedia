-- Prove2me | Theorems.Thm_FlowsNetworks_Graphs_menger_node_disjoint_chains
-- name    : FlowsNetworks.Graphs.menger_node_disjoint_chains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:53.937193+00:00
-- url     : https://prove2.me/theorems/114e8c90-d981-48fe-9ec6-ca84da12e242
-- title:
--   Chapter II, Theorem 4.2 — Menger's theorem for node disjoint chains from $S$ to $T$
-- statement:
--   Let $G = [N; \mathcal A]$ be a finite directed graph and let $S$ and $T$ be two disjoint subsets of its nodes. A **chain from $S$ to $T$** is a sequence of at least two distinct nodes, each consecutive pair an arc of $G$, starting in $S$ and ending in $T$; an **$S, T$ disconnecting set of nodes** is a node set meeting every chain from $S$ to $T$.
--
--   Then the maximal number of pairwise node disjoint chains from $S$ to $T$ equals the minimal number of nodes in an $S, T$ disconnecting set:
--   $$\max\{k : \text{there are } k \text{ pairwise node disjoint chains from } S \text{ to } T\} = \min\{|D| : D \text{ is an } S, T \text{ disconnecting set of nodes}\}.$$
--
--   This is Menger's theorem in its directed, node-disjoint, set-to-set form; the book derives it from the max flow min cut theorem with unit node capacities.
--
--   **Formalization Note** Both extremes are stated as attained: there is a $k$ that is the greatest number of pairwise node disjoint chains (a family `Fin k → List N` of chains no two of which share a node) and the least size of a disconnecting set. Pairwise node disjoint means no common node at all, endpoints included. Nodes of $S$ and $T$ may belong to a disconnecting set.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, p. 34, Theorem 4.2

import Mathlib
import Definitions.Def_FlowsNetworks_Graphs_Chains

namespace FlowsNetworks.Graphs

/-- Ford–Fulkerson, *Flows in Networks*, Chapter II, Theorem 4.2 (Menger, p. 34). Let `S` and `T`
be two disjoint subsets of the nodes of the graph `G = [N; 𝒜]`. The maximal number of pairwise
node disjoint chains from `S` to `T` is equal to the minimal number of nodes in an `S, T`
disconnecting set of nodes. Both extremes are stated as attained, with a common value `k`. -/
theorem menger_node_disjoint_chains {N : Type} [Fintype N] [DecidableEq N] (G : Digraph N)
    (S T : Finset N) (hST : Disjoint S T) :
    ∃ k : ℕ,
      IsGreatest {m : ℕ | ∃ C : Fin m → List N, (∀ i, G.IsChainFromTo S T (C i)) ∧
          ∀ i j, i ≠ j → ∀ v ∈ C i, v ∉ C j} k ∧
      IsLeast {m : ℕ | ∃ D : Finset N, G.IsDisconnecting S T D ∧ D.card = m} k := by sorry

end FlowsNetworks.Graphs
