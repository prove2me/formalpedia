-- Prove2me | Theorems.Thm_DiestelGraphTheory_jordan_curve_polygon
-- name    : DiestelGraphTheory.jordan_curve_polygon
-- status  : Proved
-- author  : @tiago duque marques
-- created : 2026-11-18T11:35:24.202666+00:00
-- url     : https://prove2.me/theorems/a38fd4f2-f275-4dbe-abb2-c7b0458f9216
-- title:
--   Jordan Curve Theorem for polygons (Diestel, Theorem 4.1.1)
-- statement:
--   Let $P\subseteq\mathbb R^2$ be a polygon, i.e. a union of finitely many straight line segments that is homeomorphic to the unit circle. Then $\mathbb R^2\setminus P$ has exactly two regions (classes of points linked by polygonal arcs avoiding $P$), and
--
--   $$\partial O = P \quad\text{for each region } O \text{ of } \mathbb R^2\setminus P.$$
--
--   This is the topological fact on which the theory of plane graphs in Diestel's Chapter 4 rests: it is used to show that cycles separate the plane and that edges on cycles lie on the frontier of two faces.
--
--   **Formalization Note** The number of regions is `Nat.card` of the set of regions, so the statement also asserts that this set is finite.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Theorem 4.1.1, p. 95.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc

namespace DiestelGraphTheory
theorem jordan_curve_polygon (P : Set (ℝ × ℝ)) (hP : IsPolygon P) :
    Nat.card (regions Pᶜ) = 2 ∧ ∀ O ∈ regions Pᶜ, frontier O = P := by sorry
end DiestelGraphTheory
