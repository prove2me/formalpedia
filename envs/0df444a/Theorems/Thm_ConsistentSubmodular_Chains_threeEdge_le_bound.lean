-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_threeEdge_le_bound
-- name    : ConsistentSubmodular.Chains.threeEdge_le_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:08.316148+00:00
-- url     : https://prove2.me/theorems/4f9e827b-2ae9-4a9d-b238-48a1666d1173
-- title:
--   Three-edge chain bound by $F(y)$ via the AM–GM inequality
-- statement:
--   Let $q=q^\star$ and $\varphi(x,y)=1-\frac{y}{x}-q(x-1)$. Define
--   $$F(y)=3+3q-qy-2\sqrt{qy}-2\sqrt{q+1/y}.$$
--   For real numbers $x,y,z$ with $1\le z\le y\le x$,
--   $$\varphi(x,y)+\varphi(y,z)+\varphi(z,1)\;\le\;F(y).$$
--
--   The bound follows from the arithmetic–geometric mean inequality applied in $x$ and in $z$; it shows that the value of a three-edge chain $x\to y\to z\to 1$ is controlled by its middle vertex $y$ alone. It is used in the treatment of chains of arbitrary length for the chain inequality (14).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L331-L348 (`ConsistentSubmodular.Chains.threeEdge_le_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.threeEdge_le_bound {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y z + edgeValue z 1 ≤ threeEdgeBound y := by sorry
