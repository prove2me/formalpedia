-- Prove2me | Theorems.Thm_DiestelGraphTheory_triangulation_edges
-- name    : DiestelGraphTheory.triangulation_edges
-- status  : Open
-- author  : @tiago duque marques
-- created : 2026-11-18T11:37:05.813208+00:00
-- url     : https://prove2.me/theorems/94946bdc-ac6a-47ed-a862-7f2847d41cff
-- title:
--   A plane triangulation with $n$ vertices has $3n-6$ edges (Diestel, Corollary 4.2.10)
-- statement:
--   Let $G$ be a plane triangulation, i.e. a plane graph each of whose faces, including the outer face, is bounded by a triangle of $G$. If $G$ has $n$ vertices and $m$ edges, then
--
--   $$m=3n-6.$$
--
--   Together with the fact that maximal plane graphs are triangulations, this gives the edge bound for all plane graphs.
--
--   **Formalization Note** $3n-6$ is natural-number subtraction; every plane triangulation has at least $3$ vertices (a graph with fewer has a face whose frontier is not a triangle), so it is exact.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Corollary 4.2.10 (second assertion), p. 102; plane triangulation defined on p. 100.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Definitions.Def_DiestelGraphTheory_PlaneGraph

namespace DiestelGraphTheory
theorem triangulation_edges (G : PlaneGraph) (hG : G.IsTriangulation) :
    Nat.card G.E = 3 * Nat.card G.V - 6 := by sorry
end DiestelGraphTheory
