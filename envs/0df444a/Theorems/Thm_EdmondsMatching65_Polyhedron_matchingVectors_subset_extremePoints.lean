-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_matchingVectors_subset_extremePoints
-- name    : EdmondsMatching65.Polyhedron.matchingVectors_subset_extremePoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:44:14.387987+00:00
-- url     : https://prove2.me/theorems/600608b0-9328-437d-beda-bd9769e80e31
-- title:
--   §2, p. 126 — every matching vector is a vertex (extreme point) of the polyhedron C
-- statement:
--   Let $G$ be a finite graph, $C\subseteq\mathbb R^E$ the polyhedron of inequalities (1)–(3), and $P$ the set of matching vectors (0–1 vectors satisfying (2)). Then every matching vector belongs to $C$ and is an extreme point of $C$:
--   $$P\subseteq\operatorname{ext}(C).$$
--   That is, each $x\in P$ lies in $C$ and does not lie halfway (more generally, strictly between) two other points of $C$.
--
--   This is the easy inclusion of Theorem (P); the content of Theorem (P) is the reverse inclusion.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 126, §2, paragraph after Theorem (P)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_MatchingPolyhedron

namespace EdmondsMatching65.Polyhedron

theorem matchingVectors_subset_extremePoints {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) :
    matchingVectors G ⊆ Set.extremePoints ℝ (matchingPolyhedron G) := by sorry

end EdmondsMatching65.Polyhedron
