-- Prove2me | Theorems.Thm_DiestelGraphTheory_plane_edges_le
-- name    : DiestelGraphTheory.plane_edges_le
-- status  : Open
-- author  : @tiago duque marques
-- created : 2026-11-18T11:36:33.550937+00:00
-- url     : https://prove2.me/theorems/d0ed5227-699e-4980-a609-7f52f33e47a2
-- title:
--   A plane graph with $n\ge3$ vertices has at most $3n-6$ edges (Diestel, Corollary 4.2.10)
-- statement:
--   Let $G$ be a plane graph with $n\ge3$ vertices and $m$ edges. Then
--
--   $$m\le 3n-6.$$
--
--   No connectedness is assumed. This bound is what forces every planar graph to have a vertex of degree at most $5$, and it shows that $K_5$ is not planar.
--
--   **Formalization Note** Since $n\ge3$, the natural-number subtraction $3n-6$ is exact.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Corollary 4.2.10 (first assertion), p. 102.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Definitions.Def_DiestelGraphTheory_PlaneGraph

namespace DiestelGraphTheory
theorem plane_edges_le (G : PlaneGraph) (hn : 3 ≤ Nat.card G.V) :
    Nat.card G.E ≤ 3 * Nat.card G.V - 6 := by sorry
end DiestelGraphTheory
