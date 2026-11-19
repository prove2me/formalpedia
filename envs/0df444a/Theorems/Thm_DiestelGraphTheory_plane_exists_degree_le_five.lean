-- Prove2me | Theorems.Thm_DiestelGraphTheory_plane_exists_degree_le_five
-- name    : DiestelGraphTheory.plane_exists_degree_le_five
-- status  : Open
-- author  : @tiago duque marques
-- created : 2026-11-18T11:37:44.579502+00:00
-- url     : https://prove2.me/theorems/e20a28b5-66d7-4aeb-9e2a-76859b648b93
-- title:
--   Every non-empty plane graph has a vertex of degree at most $5$
-- statement:
--   Let $G$ be a plane graph with at least one vertex. Then some vertex $v$ of $G$ satisfies
--
--   $$d_G(v)\le 5,$$
--
--   where $d_G(v)$ is the number of neighbours of $v$ in the abstract graph of $G$.
--
--   This is the step of the five colour proof that removes a vertex and applies induction; it is where Euler's formula enters the colouring argument.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Proof of Proposition 5.1.2 (first proof), p. 124: d(G) = 2m/n <= 2(3n-6)/n < 6, so some vertex has degree at most 5.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Definitions.Def_DiestelGraphTheory_PlaneGraph

namespace DiestelGraphTheory
theorem plane_exists_degree_le_five (G : PlaneGraph) (hne : G.V.Nonempty) :
    ∃ v : G.V, Nat.card (G.toSimpleGraph.neighborSet v) ≤ 5 := by sorry
end DiestelGraphTheory
