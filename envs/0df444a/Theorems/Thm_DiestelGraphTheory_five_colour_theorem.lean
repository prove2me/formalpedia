-- Prove2me | Theorems.Thm_DiestelGraphTheory_five_colour_theorem
-- name    : DiestelGraphTheory.five_colour_theorem
-- status  : Open
-- author  : @tiago duque marques
-- created : 2026-11-18T11:38:27.540676+00:00
-- url     : https://prove2.me/theorems/e528a128-1d2e-4eab-bcce-e77cd3238775
-- title:
--   Five Colour Theorem (Diestel, Proposition 5.1.2)
-- statement:
--   Let $G$ be a finite simple graph. If $G$ is planar, i.e. isomorphic to the abstract graph of a plane graph whose edges are polygonal arcs, then $G$ is $5$-colourable: there is a map
--
--   $$c : V(G)\to\{1,2,3,4,5\}\quad\text{with}\quad c(u)\ne c(v) \text{ whenever } uv\in E(G).$$
--
--   This is the strongest colouring bound for planar graphs with a short proof; the Four Colour Theorem improves $5$ to $4$.
--
--   **Formalization Note** $5$-colourability is Mathlib's `SimpleGraph.Colorable 5`. The vertex type is assumed finite, as are all graphs in Diestel.
-- source:
--   R. Diestel, Graph Theory, 6th ed., Springer GTM 173 (2025), https://diestel-graph-theory.com/basic.html (free preview of Ch. 4-5). Proposition 5.1.2 (Five Colour Theorem), p. 124; k-colourable defined at the start of Ch. 5; planar defined in Section 4.4.

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Definitions.Def_DiestelGraphTheory_PlaneGraph

namespace DiestelGraphTheory
theorem five_colour_theorem {V : Type*} [Finite V] (G : SimpleGraph V) (hG : IsPlanar G) :
    G.Colorable 5 := by sorry
end DiestelGraphTheory
