-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_hasDerivAt_twoEdgeRatio_fst
-- name    : ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:50.324377+00:00
-- url     : https://prove2.me/theorems/e961bb90-0204-43c9-b20f-5c52d7b27f00
-- title:
--   Partial derivative of the two-edge ratio $R(x,y)$ in $x$
-- statement:
--   Let $R(x,y)=\dfrac{2-y/x-1/y}{x+y-1}$. For $x>0$ and $x+y-1\ne0$, the function $t\mapsto R(t,y)$ is differentiable at $x$ with derivative
--   $$\frac{\partial R}{\partial x}(x,y)=\frac{\dfrac{y}{x^2}(x+y-1)-\Big(2-\dfrac yx-\dfrac1y\Big)}{(x+y-1)^2}.$$
--
--   This is a calculus step used to locate the interior maximum of $R$ on the region $\{1\le y\le x\le8\}$, needed for inequality (15).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L91-L105 (`ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_fst`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_fst {x y : ℝ} (hx : 0 < x) (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun t => twoEdgeRatio t y)
      ((y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) x := by sorry
