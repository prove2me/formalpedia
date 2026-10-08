-- Prove2me | Theorems.Thm_Balinski61_Whitney_whitney_theorem
-- name    : Balinski61.Whitney.whitney_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:04:56.830732+00:00
-- url     : https://prove2.me/theorems/b1108d71-5369-4e26-8bb0-e5a2238f0bb0
-- title:
--   WHITNEY'S THEOREM — a graph is n-tuply connected iff any two points are joined by n disjoint paths
-- statement:
--   Let $G$ be a finite graph with at least two points and let $n \ge 0$ be an integer. Then $G$ is $n$-tuply connected (at least $n+1$ points, and connected after deleting any $n-1$ or fewer points) if and only if, for every pair of distinct points $p_s, p_k$, there are $n$ disjoint paths from $p_s$ to $p_k$ — $n$ pairwise distinct simple paths no two of which share a point other than $p_s$ and $p_k$:
--   $$
--   G \text{ is } n\text{-tuply connected} \iff \forall\, p_s \ne p_k:\ G \text{ has } n \text{ disjoint } p_s\text{–}p_k \text{ paths}.
--   $$
--
--   This is Whitney's 1932 characterization of vertex connectivity (the vertex form of Menger's theorem). Balinski gives a proof of the "only if" direction from the max-flow min-cut theorem with point and line capacities, and combines it with his theorem on polytope graphs to obtain $n$ disjoint paths between any two vertices of a bounded full-dimensional polyhedron in $n$-space.
--
--   **Formalization Note** The hypothesis $|V| \ge 2$ is added: the paper's "any pair of points" presupposes two points, and without it the equivalence fails for a one-point graph and $n \ge 1$. Paths are required to be pairwise distinct and simple; see the definition file. No assumption $n \ge 1$ is made: for $n = 0$ both sides hold for every graph with at least one point.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, WHITNEY'S THEOREM

import Mathlib
import Definitions.Def_Balinski61_Whitney_Graph

namespace Balinski61.Whitney

theorem whitney_theorem {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ)
    (hcard : 2 ≤ Fintype.card V) :
    IsNTuplyConnected G n ↔ ∀ ps pk : V, ps ≠ pk → HasNDisjointPaths G n ps pk := by sorry

end Balinski61.Whitney
