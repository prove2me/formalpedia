-- Prove2me | Theorems.Thm_BalancedGames_Comb_theorem_11
-- name    : BalancedGames.Comb.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:18.98192+00:00
-- url     : https://prove2.me/theorems/fba03912-0b12-4769-bb87-3649ffff168c
-- title:
--   Theorem 11, p. 18 (Naddef–Pulleyblank [14]) — the adjacency graph of a combinatorial polytope is a hypercube or Hamilton-connected
-- statement:
--   Let $\iota$ be a finite index set and let $P\subseteq\mathbb R^{\iota}$ be a polytope (the convex hull of finitely many points) that is **combinatorial** in the sense of Definition 1: all its vertices are 0-1-valued, and any two distinct non-adjacent vertices $v_1,v_2$ admit two other different vertices $v_3,v_4$ with $v_1+v_2=v_3+v_4$. Let $G$ be the adjacency graph of $P$ (vertices of $P$ as nodes, edges of $P$ as edges). Then
--
--   $$G\cong Q_d\ \text{for some } d\ge0 \qquad\text{or}\qquad G \text{ is Hamilton-connected.}$$
--
--   This is the theorem of Naddef and Pulleyblank (J. Combin. Theory Ser. B 31 (1981)), quoted without proof in the paper. Combined with the facts that $\mathcal{BG}_+(n)$ is combinatorial and its graph is not a hypercube for $n\ge2$, it gives the Hamilton-connectedness of Theorem 12.
--
--   **Formalization Note** $Q_d$ is the graph on $\{0,1\}^d$ with adjacency at Hamming distance $1$, and "is a hypercube" means graph-isomorphic to some $Q_d$ (including $Q_0$, one node). Hamilton-connected means every two distinct nodes are joined by a walk visiting every node exactly once.
--
--   Differences from the source:
--   - encoding: polytope in $\mathbb R^d$ → convex hull of a finite set in $\mathbb R^{\iota}$ for a finite type $\iota$; reason: $\mathbb R^{\iota}\cong\mathbb R^{|\iota|}$ coordinatewise, and convex hulls of finite sets are exactly the polytopes (Minkowski–Weyl).
--   - reading: Definition 1, "given two vertices $v_1,v_2$ of $P$, if they are not adjacent" → two **distinct** non-adjacent vertices; reason: for $v_1=v_2$ the condition would require $2v_1=v_3+v_4$ with $v_3\neq v_4$, impossible at a vertex, so the literal reading makes no polytope with a vertex combinatorial.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, p. 18, Theorem 11 (citing [14] D. Naddef, W. R. Pulleyblank, Hamiltonicity and combinatorial polyhedra, J. Combin. Theory Ser. B 31 (1981) 297–312)

import Mathlib
import Definitions.Def_BalancedGames_Comb_Basic

namespace BalancedGames.Comb

/-- **Theorem 11** (p. 18; Naddef–Pulleyblank [14]). The adjacency graph of a combinatorial
polytope `P ⊆ ℝ^ι` (`ι` finite) is a hypercube or Hamilton-connected. -/
theorem theorem_11 {ι : Type} [Fintype ι] (P : Set (ι → ℝ)) (hP : IsPolytope P)
    (hC : IsCombinatorial P) :
    IsHypercube (adjGraph P) ∨ IsHamiltonConnected (adjGraph P) := by sorry

end BalancedGames.Comb
