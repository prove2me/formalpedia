-- Prove2me | Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_edge
-- name    : ConsistentSubmodular.PolygonalPath.subdivide_edge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:49.897646+00:00
-- url     : https://prove2.me/theorems/c33f8e37-02dc-4592-ab99-8b40e90c2c8c
-- title:
--   Each segment of the subdivided path lies inside one old segment
-- statement:
--   Let $\gamma$ be a polygonal path with nodes $\gamma_0,\dots,\gamma_\ell$, let $N\ge 1$ and let $\gamma^{(N)}$ be its uniform $N$-fold subdivision (with $\ell N$ segments). Then for every segment $j$ of $\gamma^{(N)}$ there exist an old segment $a<\ell$ and an integer $r<N$ such that the endpoints of segment $j$ are
--   $$\gamma^{(N)}_j=(1-\tfrac rN)\gamma_a+\tfrac rN\gamma_{a+1},\qquad
--   \gamma^{(N)}_{j+1}=\bigl(1-\tfrac{r+1}{N}\bigr)\gamma_a+\tfrac{r+1}{N}\gamma_{a+1}.$$
--
--   Both endpoints of each new edge are therefore points of the same old edge $[\gamma_a,\gamma_{a+1}]$. This guarantees that any property holding along the old edges holds along the new ones.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PathSubdivision.lean#L101-L126 (`ConsistentSubmodular.PolygonalPath.subdivide_edge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem ConsistentSubmodular.PolygonalPath.subdivide_edge (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (j : Fin (γ.subdivide N).pieces) :
    ∃ (a : Fin γ.pieces) (r : ℕ), r < N ∧
      (γ.subdivide N).node j.castSucc =
        mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) ∧
      (γ.subdivide N).node j.succ =
        mix (γ.node a.castSucc) (γ.node a.succ) (((r : ℝ) + 1) / N) := by sorry
