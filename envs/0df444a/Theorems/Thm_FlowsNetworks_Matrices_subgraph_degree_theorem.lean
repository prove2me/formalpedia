-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_subgraph_degree_theorem
-- name    : FlowsNetworks.Matrices.subgraph_degree_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:01.074996+00:00
-- url     : https://prove2.me/theorems/523eb564-1c88-4ed1-bf95-cb335d2b2226
-- title:
--   Chapter II, Theorem 11.1 — subgraphs of a directed graph with local degrees between bounds
-- statement:
--   Let $G = [N; \mathcal A]$ be a finite directed graph (no loops, at most one arc from $x$ to $y$). For a subgraph $H$ write $i_H(x)$ and $e_H(x)$ for the numbers of arcs of $H$ issuing from and entering the node $x$. For $X \subseteq N$ let $A(X)$ be the set of nodes $y$ with an arc from $X$ to $y$, $B(X)$ the set of nodes $y$ with an arc from $y$ into $X$, and $|(X, y)|$, $|(y, X)|$ the numbers of arcs from $X$ to $y$ and from $y$ to $X$. For a function $g$ on nodes write $g(X) = \sum_{x \in X} g(x)$.
--
--   Suppose that to each node $x$ there correspond integers $a(x), a'(x), b(x), b'(x)$ with
--   $$0 \le a(x) \le a'(x), \qquad 0 \le b(x) \le b'(x).$$
--   Then $G$ has a subgraph $H$ with
--   $$a(x) \le i_H(x) \le a'(x), \qquad b(x) \le e_H(x) \le b'(x) \qquad (x \in N)$$
--   if and only if, for all $X \subseteq N$,
--   $$a(X) \le \sum_{y \in A(X)} \min\big[b'(y), |(X, y)|\big] \quad\text{and}\quad b(X) \le \sum_{y \in B(X)} \min\big[a'(y), |(y, X)|\big].$$
--
--   The theorem is a two-sided extension of Ore's solution of the subgraph problem for directed graphs (Corollary 11.2) and, for the complete directed graph on $n$ nodes, contains the existence problem for $n \times n$ $(0, 1)$-matrices with zero trace.
--
--   **Formalization Note** The integer bounds are natural numbers, which builds in $0 \le a(x)$ and $0 \le b(x)$; the hypotheses $a \le a'$ and $b \le b'$ are explicit. A subgraph is its arc set $H \subseteq \mathcal A$. Both conditions are required for every finite set $X \subseteq N$, including $X = \emptyset$ and $X = N$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 73–74, Theorem 11.1

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_Digraph

namespace FlowsNetworks.Matrices

/-- Chapter II, Theorem 11.1 (Ford–Fulkerson, *Flows in Networks*, pp. 73–74). Let `G = [N; 𝒜]`
be a directed graph and suppose that, to each node `x`, there correspond integers
`0 ≤ a(x) ≤ a′(x)` and `0 ≤ b(x) ≤ b′(x)` (11.10)–(11.11) (nonnegative integers are natural
numbers here). Then `G` has a subgraph `H` whose local degrees satisfy
`a(x) ≤ i_H(x) ≤ a′(x)` (11.12) and `b(x) ≤ e_H(x) ≤ b′(x)` (11.13) if and only if, for all
`X ⊆ N`, (11.14) `a(X) ≤ ∑_{y ∈ A(X)} min[b′(y), |(X, y)|]` and
(11.15) `b(X) ≤ ∑_{y ∈ B(X)} min[a′(y), |(y, X)|]`. -/
theorem subgraph_degree_theorem {N : Type} [Fintype N] [DecidableEq N] (G : Digraph N)
    (a a' b b' : N → ℕ) (ha : ∀ x, a x ≤ a' x) (hb : ∀ x, b x ≤ b' x) :
    (∃ H : Finset (N × N), IsSubgraph G H ∧
        ∀ x, (a x ≤ outDeg H x ∧ outDeg H x ≤ a' x) ∧ (b x ≤ inDeg H x ∧ inDeg H x ≤ b' x)) ↔
      ∀ X : Finset N,
        (∑ x ∈ X, a x ≤ ∑ y ∈ succSet G X, min (b' y) (numArcsTo G X y)) ∧
        (∑ x ∈ X, b x ≤ ∑ y ∈ predSet G X, min (a' y) (numArcsFrom G y X)) := by sorry

end FlowsNetworks.Matrices
