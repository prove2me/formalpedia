-- Prove2me | Theorems.Thm_DelaunayStretch_theorem_2_4_reduction
-- name    : DelaunayStretch.theorem_2_4_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:52.735254+00:00
-- url     : https://prove2.me/theorems/bdc9876a-ff34-4472-b241-3ec6628a077f
-- title:
--   Theorem 2.4 — the chain inequality at level $U$ implies $d_D(u,v)\le U\|u-v\|$
-- statement:
--   Let $U\in\mathbb R$, and suppose that the chain inequality holds at level $U$. Then, for every finite set $S\subset\mathbb R^2$, every Delaunay triangulation $D$ of $S$, and all $u,v\in S$,
--
--   $$
--   d_D(u,v)\le U\,\|u-v\| .
--   $$
--
--   This reduces the stretch bound for Delaunay triangulations to the chain inequality for disk chains.
--
--   **Formalization Note** $d_D(u,v)\le U\|u-v\|$ is stated as the existence of a walk along edges of $D$ from $u$ to $v$ of Euclidean length at most $U\|u-v\|$.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: d_D(u, v) ≤ c‖u − v‖ with d_D the shortest-path length along the edges of D → there is a walk from u to v in the edge graph of D of Euclidean length ≤ c‖u − v‖; reason: a shortest path exists in the finite graph, so the two statements are equivalent; avoids an infimum over a possibly empty set
--   - encoding: P(u, v), the length of a shortest path from u to v in the ladder graph → the infimum of the weights of walks from u to v in the ladder graph (vertex labels, not points); reason: the ladder graph is finite with nonnegative weights (rails by (C4) and (2.1)), so the infimum is attained and is the shortest-path length
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem 2.4, p.13 (proof Appendix A, p.52)

import Mathlib
import Definitions.Def_DelaunayStretch_ChainInequality
import Definitions.Def_DelaunayStretch_IsDelaunayTriangulation
import Definitions.Def_DelaunayStretch_delaunayGraph

namespace DelaunayStretch

/-- **Theorem 2.4 (Reduction to disk chains)** (p.13; proof in Appendix A, p.52). Let `U ∈ ℝ`,
and suppose that the chain inequality holds at level `U`. Then, for every finite set
`S ⊂ ℝ²`, every Delaunay triangulation `D` of `S`, and all `u, v ∈ S`,
`d_D(u, v) ≤ U ‖u − v‖`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem 2.4, p.13.

**Formalization Note** `d_D(u, v) ≤ U ‖u − v‖` is the existence of a walk along edges of `D`
of length at most `U ‖u − v‖`. -/
theorem theorem_2_4_reduction (U : ℝ) (hU : ChainInequality U) (S : Finset ℂ)
    (D : Finset (Finset ℂ)) (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S)
    (hv : v ∈ S) :
    ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ U * dist u v := by sorry

end DelaunayStretch
