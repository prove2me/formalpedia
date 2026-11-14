-- Prove2me | Theorems.Thm_ConsistentSubmodular_PolygonalPath_subdivide_node_in_segment
-- name    : ConsistentSubmodular.PolygonalPath.subdivide_node_in_segment
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:43.801546+00:00
-- url     : https://prove2.me/theorems/7ca37722-6c72-4a54-871b-623f160cbd02
-- title:
--   Nodes of the uniform subdivision of a polygonal path lie on the old segments at fractions $r/N$
-- statement:
--   Let $\gamma$ be a polygonal path in $\mathbb R^{m+1}$ with $\ell$ segments and nodes $\gamma_0,\dots,\gamma_\ell$, and let $N\ge 1$. Let $\gamma^{(N)}$ be the path obtained by dividing every segment uniformly into $N$ pieces, so that it has $\ell N$ segments. Then for every old segment $a<\ell$ and every $r$ with $0\le r\le N$, the node of $\gamma^{(N)}$ with index $aN+r$ is
--   $$\gamma^{(N)}_{aN+r}\;=\;(1-\tfrac rN)\,\gamma_a+\tfrac rN\,\gamma_{a+1}.$$
--
--   The statement includes $r=N$, where the node coincides with the next old node $\gamma_{a+1}$, so the right endpoint of a refined segment is always expressed through its own old segment. It is used to show that the refined path follows the same edges as the original.
--
--   **Formalization Note**: nodes are indexed in `Fin (pieces + 1)`; the index $aN+r$ is shown to be in range via `subdivide_pieces`.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PathSubdivision.lean#L53-L82 (`ConsistentSubmodular.PolygonalPath.subdivide_node_in_segment`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem ConsistentSubmodular.PolygonalPath.subdivide_node_in_segment (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (a : Fin γ.pieces) (r : ℕ) (hr : r ≤ N) :
    (γ.subdivide N).node ⟨a.val * N + r, by
      dsimp only [subdivide_pieces]
      have := a.isLt
      nlinarith⟩ = mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) := by sorry
