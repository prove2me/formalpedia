-- Prove2me | Theorems.Thm_DiestelGraphTheory_euler_formula
-- name    : DiestelGraphTheory.euler_formula
-- status  : Open
-- author  : @tiago duque marques
-- created : 2026-11-18T11:35:58.296438+00:00
-- url     : https://prove2.me/theorems/d661e285-44da-4325-834a-13053edca622
-- title:
--   Euler's formula (Diestel, Theorem 4.2.9)
-- statement:
--   Let $G$ be a connected plane graph with $n$ vertices, $m$ edges and $\ell$ faces (regions of $\mathbb R^2\setminus G$). Then
--
--   $$n-m+\ell=2.$$
--
--   Euler's formula is the basic counting identity for plane graphs; it yields the edge bound $m\le 3n-6$ and hence the existence of a vertex of degree at most $5$.
--
--   **Formalization Note** Connectedness is that of the abstract graph and, as in Diestel, includes non-emptiness. The identity is stated in $\mathbb Z$; $\ell$ is `Nat.card` of the set of faces, so the statement also asserts that there are finitely many faces.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Theorem 4.2.9, p. 101.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Definitions.Def_DiestelGraphTheory_PlaneGraph

namespace DiestelGraphTheory
theorem euler_formula (G : PlaneGraph) (hG : G.toSimpleGraph.Connected) :
    (Nat.card G.V : ℤ) - Nat.card G.E + Nat.card G.faces = 2 := by sorry
end DiestelGraphTheory
