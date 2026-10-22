-- Prove2me | Theorems.Thm_FlowsNetworks_Matrices_ore_subgraph_theorem
-- name    : FlowsNetworks.Matrices.ore_subgraph_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:14.742313+00:00
-- url     : https://prove2.me/theorems/36708691-91dd-418c-913b-77f7b8b71c3c
-- title:
--   Chapter II, Corollary 11.2 — Ore's theorem on subgraphs with prescribed local degrees
-- statement:
--   Let $G = [N; \mathcal A]$ be a finite directed graph (no loops, at most one arc from $x$ to $y$), with $i_H(x)$, $e_H(x)$, $A(X)$ and $|(X, y)|$ as in Theorem 11.1, and let $a(x) \ge 0$, $b(x) \ge 0$ be integers given at every node $x$, with $a(X) = \sum_{x \in X} a(x)$ and $b(X) = \sum_{x \in X} b(x)$.
--
--   Then $G$ has a subgraph $H$ with local degrees
--   $$i_H(x) = a(x), \qquad e_H(x) = b(x) \qquad (x \in N)$$
--   if and only if
--   $$a(N) = b(N) \quad\text{and}\quad a(X) \le \sum_{y \in A(X)} \min\big[b(y), |(X, y)|\big] \quad\text{for all } X \subseteq N.$$
--
--   This is Ore's theorem on the subgraph problem for directed graphs: a single family of inequalities over node sets, together with the balance condition, decides whether prescribed in- and out-degrees are realized by a subgraph.
--
--   **Formalization Note** The prescribed degrees are natural numbers. The page prints $\min[b'(y), |(X, y)|]$ in (11.19); in this corollary the degrees are prescribed exactly ($a' = a$, $b' = b$, as in the discussion on p. 72 that leads to it), so $b'(y)$ is read as $b(y)$. The page also prints the summation range of (11.19) as $y \in A(x)$, with a lower-case $x$; as in (11.14) it is read as $A(X)$, the only reading in which the inequality is about the set $X$.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter II, pp. 74–75, Corollary 11.2

import Mathlib
import Definitions.Def_FlowsNetworks_Matrices_Digraph

namespace FlowsNetworks.Matrices

/-- Chapter II, Corollary 11.2 (Ore's theorem; Ford–Fulkerson, *Flows in Networks*, pp. 74–75).
The directed graph `G = [N; 𝒜]` has a subgraph `H` with local degrees `i_H(x) = a(x) ≥ 0` (11.16)
and `e_H(x) = b(x) ≥ 0` (11.17) if and only if `a(N) = b(N)` (11.18) and, for all `X ⊆ N`,
(11.19) `a(X) ≤ ∑_{y ∈ A(X)} min[b(y), |(X, y)|]`. The page prints `b′(y)` in (11.19); in the
corollary the bounds are exact (`a′ = a`, `b′ = b`, p. 72), so `b′(y)` is read as `b(y)`. -/
theorem ore_subgraph_theorem {N : Type} [Fintype N] [DecidableEq N] (G : Digraph N)
    (a b : N → ℕ) :
    (∃ H : Finset (N × N), IsSubgraph G H ∧ ∀ x, outDeg H x = a x ∧ inDeg H x = b x) ↔
      (∑ x, a x = ∑ x, b x) ∧
        ∀ X : Finset N, ∑ x ∈ X, a x ≤ ∑ y ∈ succSet G X, min (b y) (numArcsTo G X y) := by sorry

end FlowsNetworks.Matrices
