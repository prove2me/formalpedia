-- Prove2me | Theorems.Thm_ConsistentSubmodular_PolygonalPath_Along_subdivide
-- name    : ConsistentSubmodular.PolygonalPath.Along.subdivide
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:03.661717+00:00
-- url     : https://prove2.me/theorems/9a532aa5-2067-483d-a415-e2946e42cdbb
-- title:
--   Subdividing a polygonal path preserves properties holding along it
-- statement:
--   Let $\gamma$ be a polygonal path in $\mathbb R^{m+1}$ and let $\Phi$ be a property of points. Suppose $\Phi$ holds along $\gamma$, i.e. at every node $\gamma_i$ and at every point $(1-x)\gamma_i+x\gamma_{i+1}$ of every segment, $0\le x\le 1$. Then for every $N\ge 1$, $\Phi$ holds along the uniform $N$-fold subdivision $\gamma^{(N)}$ as well.
--
--   Subdividing a path never leaves a region (a simplex, a safe set) that the original path stays in. It is used to make all segments short while keeping the certificate property.
--
--   **Formalization Note**: "holds along" includes the nodes, so a path with zero segments is not vacuous.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PathSubdivision.lean#L128-L157 (`ConsistentSubmodular.PolygonalPath.Along.subdivide`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
open ConsistentSubmodular.PolygonalPath

theorem ConsistentSubmodular.PolygonalPath.Along.subdivide {γ : PolygonalPath m} {Φ : Point m → Prop}
    (hγ : γ.Along Φ) (N : ℕ) (hN : 0 < N) : (γ.subdivide N).Along Φ := by sorry
