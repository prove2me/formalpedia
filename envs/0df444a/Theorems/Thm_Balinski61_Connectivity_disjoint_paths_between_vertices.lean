-- Prove2me | Theorems.Thm_Balinski61_Connectivity_disjoint_paths_between_vertices
-- name    : Balinski61.Connectivity.disjoint_paths_between_vertices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:51:00.894026+00:00
-- url     : https://prove2.me/theorems/f762a10e-14c5-4b51-9ef6-2763fa26bf0c
-- title:
--   COROLLARY, p. 434 — any two vertices of S are joined by n disjoint paths
-- statement:
--   Let $S=\{x\in\mathbb R^n:\langle a_i,x\rangle\le b_i,\ i=1,\dots,m\}$ satisfy Balinski's standing assumptions: the only solution to $AX\le0$ is $X=0$, and some $X^0$ satisfies $AX^0<b$. Let $G(S)$ be the graph of its vertices and edges. Then for any two distinct vertices $u\neq v$ of $S$ there are $n$ pairwise distinct paths $P_1,\dots,P_n$ in $G(S)$ from $u$ to $v$, none visiting a point twice, such that
--   $$P_i\cap P_j\subseteq\{u,v\}\qquad(i\neq j).$$
--
--   This is the COROLLARY of the paper ("There exist at least $n$ disjoint paths between any pair of vertices of the polyhedral convex set $S$"), obtained by combining the THEOREM with Whitney's theorem.
--
--   **Formalization Note** "At least $n$" is stated as the existence of a family of $n$ such paths; "any pair of vertices" is read as two distinct vertices. Disjointness is `HasDisjointPaths`: the paths are `IsPath` walks, pairwise distinct, and share no point other than $u$ and $v$.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, COROLLARY

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Balinski61_Connectivity_Polyhedron
import Definitions.Def_Balinski61_Connectivity_TuplyConnected

open scoped RealInnerProductSpace

namespace Balinski61.Connectivity

theorem disjoint_paths_between_vertices (n m : ℕ)
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hS : StandingAssumptions a b)
    (u v : Set.extremePoints ℝ (Hirsch.Hpoly a b)) (huv : u ≠ v) :
    HasDisjointPaths (polyGraph (Hirsch.Hpoly a b)) u v n := by sorry

end Balinski61.Connectivity
