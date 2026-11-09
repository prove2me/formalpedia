-- Prove2me | Theorems.Thm_DelaunayStretch_theorem_1_stretch_factor
-- name    : DelaunayStretch.theorem_1_stretch_factor
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:50:37.259902+00:00
-- url     : https://prove2.me/theorems/31ff71d7-3e4c-4667-b5b6-b440e25797ab
-- title:
--   Theorem 1 — every Delaunay triangulation of a finite planar point set has stretch factor at most $1.5949$
-- statement:
--   For every finite point set $S\subset\mathbb R^2$ and every Delaunay triangulation $D$ of $S$,
--
--   $$
--   d_D(u,v)\le 1.5949\,\|u-v\|\qquad\text{for all }u,v\in S,
--   $$
--
--   where $d_D(u,v)$ is the length of a shortest path from $u$ to $v$ along the edges of $D$. This lowers the best upper bound on the worst-case stretch factor of planar Delaunay triangulations from $1.998$ (Xia, 2011) to $1.5949$, against the lower bound $1.5932$.
--
--   **Formalization Note** Delaunay triangulations are those of the formal definition (Appendix A, p.48). $1.5949=15949/10000$. The bound is stated as the existence of a walk along edges of $D$ of length at most $1.5949\|u-v\|$.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: d_D(u, v) ≤ c‖u − v‖ with d_D the shortest-path length along the edges of D → there is a walk from u to v in the edge graph of D of Euclidean length ≤ c‖u − v‖; reason: a shortest path exists in the finite graph, so the two statements are equivalent; avoids an infimum over a possibly empty set
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Theorem 1, p.4

import Mathlib
import Definitions.Def_DelaunayStretch_IsDelaunayTriangulation
import Definitions.Def_DelaunayStretch_delaunayGraph

namespace DelaunayStretch

/-- **Theorem 1** (p.4). For every finite point set `S ⊂ ℝ²` and every Delaunay triangulation
`D` of `S`, `d_D(u, v) ≤ 1.5949 ‖u − v‖` for all `u, v ∈ S`.

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Theorem 1, p.4.

**Formalization Note** The plane is `ℂ`; Delaunay triangulations are those of the formal
definition of p.48 (`IsDelaunayTriangulation`). `d_D(u, v) ≤ c ‖u − v‖` is stated as the
existence of a walk from `u` to `v` along edges of `D` of Euclidean length at most
`c ‖u − v‖` (no infimum over a possibly empty set). `1.5949 = 15949/10000`. -/
theorem theorem_1_stretch_factor (S : Finset ℂ) (D : Finset (Finset ℂ))
    (hD : IsDelaunayTriangulation S D) (u v : ℂ) (hu : u ∈ S) (hv : v ∈ S) :
    ∃ w : (delaunayGraph D).Walk u v, walkLength w ≤ (15949 / 10000 : ℝ) * dist u v := by sorry

end DelaunayStretch
