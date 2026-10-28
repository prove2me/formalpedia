-- Prove2me | Theorems.Thm_BalancedGames_Comb_theorem_12
-- name    : BalancedGames.Comb.theorem_12
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:31.599768+00:00
-- url     : https://prove2.me/theorems/9c0a9e2d-23ab-49ae-8e13-ea4b3d222c94
-- title:
--   Theorem 12, p. 19 — BG+(n) is a combinatorial polytope and its adjacency graph is Hamilton-connected
-- statement:
--   Let $N=\{1,\dots,n\}$ and let $\mathcal{BG}_+(n)$ be the polytope of balanced games $v$ (nonempty core) with $v(\varnothing)=0$, $v(S)\ge0$ for every coalition $S$, and $v(N)=1$. Then
--
--   1. $\mathcal{BG}_+(n)$ is a **combinatorial polytope** (Definition 1): it is a polytope (the convex hull of finitely many games), all its vertices are 0-1-valued, and for any two distinct non-adjacent vertices $v_1,v_2$ there are two other different vertices $v_3,v_4$ with $v_1+v_2=v_3+v_4$;
--   2. the **adjacency graph** of $\mathcal{BG}_+(n)$ is **Hamilton-connected**: any two distinct vertices are joined by a path along edges of $\mathcal{BG}_+(n)$ that visits every vertex exactly once.
--
--   $$\mathcal{BG}_+(n)\ \text{a combinatorial polytope}\quad\text{and}\quad \mathrm{G}\big(\mathcal{BG}_+(n)\big)\ \text{Hamilton-connected}.$$
--
--   The vertex set of $\mathcal{BG}_+(n)$ grows doubly exponentially in $n$, yet every pair of vertices is the pair of endpoints of a Hamiltonian path; in particular, for $n\ge2$, the graph has a Hamiltonian cycle.
--
--   **Formalization Note** Vertices are extreme points, adjacency is the published `Hirsch.Adj` (the segment is a face), and Hamilton-connected is stated with Mathlib's `Walk.IsHamiltonian` for every pair of distinct vertices. Definition 1 applies to polytopes, so the conclusion states that $\mathcal{BG}_+(n)$ is a polytope (convex hull of a finite set) alongside the two conditions of Definition 1; Proposition 1 proves that part.
--
--   Differences from the source:
--   - generalization: $N=\{1,\dots,n\}$ with $n\ge1$ implicit → every $n\in\mathbb N$; reason: at $n=0$, $\mathcal{BG}_+(0)=\varnothing$ ($v(\varnothing)=0\neq1=v(N)$) and every clause holds trivially (the empty set is the convex hull of the empty set); the statement specializes to the paper's for $n\ge1$.
--   - reading: Definition 1, "given two vertices $v_1,v_2$ of $P$, if they are not adjacent" → two **distinct** non-adjacent vertices; reason: for $v_1=v_2$ the condition would require $2v_1=v_3+v_4$ with $v_3\neq v_4$, impossible at a vertex, so the literal reading makes no polytope with a vertex combinatorial.
--   - encoding: polytope → convex hull of a finite set; reason: Minkowski–Weyl, the same sets as bounded polyhedra.
--   - encoding: game in $\mathbb R^{2^N\setminus\{\varnothing\}}$ → vector on all $2^n$ coalitions with $v(\varnothing)=0$ imposed in $\mathcal G_+(n)$; reason: an affine embedding, it preserves vertices, edges, sums and 0-1-valuedness.
--   - encoding: balanced by (4) → nonempty core; reason: p. 4 identifies the balanced games with those having a nonempty core (Theorem 1).
--   - encoding: $N=\{1,\dots,n\}$ → `Fin n` (0-based); reason: relabelling of players.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 19, Theorem 12

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Theorem 12** (p. 19). `BG+(n)` is a combinatorial polytope (Definition 1: a polytope
satisfying both conditions), and its adjacency graph is Hamilton-connected. -/
theorem theorem_12 (n : ℕ) :
    (IsPolytope (BGplus n) ∧ IsCombinatorial (BGplus n)) ∧
      IsHamiltonConnected (adjGraph (BGplus n)) := by sorry

end BalancedGames.Comb
