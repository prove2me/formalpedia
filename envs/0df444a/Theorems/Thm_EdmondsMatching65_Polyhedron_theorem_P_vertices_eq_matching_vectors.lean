-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_theorem_P_vertices_eq_matching_vectors
-- name    : EdmondsMatching65.Polyhedron.theorem_P_vertices_eq_matching_vectors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:45:14.157984+00:00
-- url     : https://prove2.me/theorems/c176cd38-3676-4835-b2ef-949a40576dd6
-- title:
--   Theorem (P), p. 126 — the vertices of the polyhedron C are exactly the matching vectors of G
-- statement:
--   Let $G$ be a finite graph with node set $V$ and edge set $E$. Let $C\subseteq\mathbb R^E$ be the polyhedron of vectors $x=(x_e)_{e\in E}$ satisfying
--
--   1. $x_e\ge 0$ for every edge $e$;
--   2. $\sum_{e\text{ meets }v}x_e\le 1$ for every node $v$;
--   3. $\sum_{e\text{ has both ends in }S}x_e\le r$ for every set $S$ of $2r+1$ nodes, $r$ a strictly positive integer;
--
--   and let $P$ be the set of matching vectors: the vectors with all components $0$ or $1$ that satisfy (2), i.e. the incidence vectors of matchings of $G$.
--
--   **Theorem (P).** $P$ is the set of vertices (extreme points) of $C$:
--   $$\operatorname{ext}(C)=P .$$
--
--   Consequently, for any real edge weights $c$, the maximum weight of a matching equals the maximum of the linear form $\sum_e c_e x_e$ over $C$: maximum-weight matching is a linear program over a polyhedron described by explicit inequalities. This is the first polyhedral description of the matching polytope of a general (non-bipartite) graph.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 126, §2, Theorem (P)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron

namespace EdmondsMatching65.Polyhedron

theorem theorem_P_vertices_eq_matching_vectors {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) :
    Set.extremePoints ℝ (matchingPolyhedron G) = matchingVectors G := by sorry

end EdmondsMatching65.Polyhedron
