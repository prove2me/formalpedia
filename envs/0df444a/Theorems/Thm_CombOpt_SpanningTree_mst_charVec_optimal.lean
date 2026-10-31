-- Prove2me | Theorems.Thm_CombOpt_SpanningTree_mst_charVec_optimal
-- name    : CombOpt.SpanningTree.mst_charVec_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:07:43.387379+00:00
-- url     : https://prove2.me/theorems/a8aa1e05-e043-4fc1-8513-875a708f9016
-- title:
--   Theorem 2.8 (Edmonds) — the characteristic vector of an MST is an optimal solution of the spanning-tree LP (corrected: nonempty node set)
-- statement:
--   Let $G=(V,E)$ be a graph with at least one node (loops and parallel edges allowed), let $c\in\mathbb R^E$ be arbitrary real edge costs, and let $T$ be a minimum spanning tree of $G$ with respect to $c$. Let $x^0$ be the characteristic vector of $T$: $x^0_e=1$ for $e\in T$ and $x^0_e=0$ otherwise. Then $x^0$ is an optimal solution of the linear program
--
--   $$\begin{aligned}
--   \text{minimize}\quad & c^{T}x && (2.1)\\
--   \text{subject to}\quad & x(\gamma(S))\le |S|-1 \quad \text{for all } S,\ \emptyset\ne S\subseteq V, && (2.2)\\
--   & x(E)=|V|-1, && (2.3)\\
--   & x_e\ge 0 \quad \text{for all } e\in E, && (2.4)
--   \end{aligned}$$
--
--   where $x(B)=\sum_{e\in B}x_e$ and $\gamma(S)$ is the set of edges with both ends in $S$. That is, $x^0$ satisfies (2.2)–(2.4) and $c^{T}x^0\le c^{T}x$ for every $x$ satisfying (2.2)–(2.4).
--
--   Hence the optimal value of the LP equals the cost of an MST. The theorem is due to Edmonds (1971) and is used in Chapter 7 for the subtour lower bound of the traveling salesman problem.
--
--   **Formalization Note** The existence of an MST makes $G$ connected. The hypothesis $|V|\ge 1$ is added: for the graph with no nodes and no edges, $\emptyset$ is an MST but its characteristic vector has $x(E)=0\ne -1=|V|-1$.
--
--   Differences from the source:
--   - correction: any graph G (|V| ≥ 0) → [Nonempty V]; reason: for V = E = ∅ the empty edge set is an MST but its characteristic vector violates (2.3), 0 ≠ −1, so the printed statement fails
--   - reading: (2.2) for all S with ∅ ≠ S ⊂ V → (2.2) for all nonempty S ⊆ V; reason: the book writes ⊂ for ⊆ also in (2.6), whose proof says 'Let A ⊆ E'; under the proper-subset reading the extra constraint for S = V is x(E) ≤ |V| − 1, implied by (2.3), so the feasible set and the theorem are the same
--   - encoding: x⁰ is an optimal solution of (2.1) → SpanningTreeLPOptimal: x⁰ feasible and cᵀx⁰ ≤ cᵀy for every feasible y; reason: the definition of an optimal solution; no infimum value is used
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.8, p. 16 (PDF p. 25)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsMST
import Definitions.Def_CombOpt_SpanningTree_Graph_SpanningTreeLPOptimal

namespace CombOpt.SpanningTree

/-- **Theorem 2.8 (Edmonds 1971): the characteristic vector of an MST is an optimal solution of
the spanning-tree linear program (2.1).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.8, p. 16 (PDF p. 25): "Let x^0 be the characteristic vector of an MST with respect
to costs c_e. Then x^0 is an optimal solution of (2.1)", where (2.1) is "Minimize c^T x subject to
x(γ(S)) ≤ |S| − 1, for all S, ∅ ≠ S ⊂ V (2.2); x(E) = |V| − 1 (2.3); x_e ≥ 0, for all e ∈ E (2.4)".

Let `G` be a finite graph (loops and parallel edges allowed) with at least one node, `c` real edge
costs, and `T` a minimum spanning tree for `c`. Let `x⁰_e = 1` for `e ∈ T` and `x⁰_e = 0`
otherwise. Then `x⁰` satisfies (2.2)–(2.4) and `c^T x⁰ ≤ c^T x` for every `x` satisfying
(2.2)–(2.4).

**Formalization Note.** The existence of an MST makes `G` connected. The node set is assumed
nonempty: with `V = E = ∅` the empty edge set is an MST but `x⁰(E) = 0 ≠ −1 = |V| − 1`, so (2.3)
fails (see the differences list). (2.2) is imposed for every nonempty `S ⊆ V`; see
`Graph.SpanningTreeLPFeasible`. -/
theorem mst_charVec_optimal {V E : Type*} [Fintype V] [Nonempty V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ) (T : Finset E) (hT : G.IsMST c T) :
    G.SpanningTreeLPOptimal c (fun e => if e ∈ T then 1 else 0) := by sorry

end CombOpt.SpanningTree
