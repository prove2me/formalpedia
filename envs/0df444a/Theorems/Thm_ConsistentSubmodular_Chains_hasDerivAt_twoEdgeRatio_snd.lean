-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_hasDerivAt_twoEdgeRatio_snd
-- name    : ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_snd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:03.782226+00:00
-- url     : https://prove2.me/theorems/bb1c07e7-589a-477d-aaed-420bf2e38e26
-- title:
--   Partial derivative of the two-edge ratio $R(x,y)$ in $y$
-- statement:
--   Let $R(x,y)=\dfrac{2-y/x-1/y}{x+y-1}$. For $x>0$, $y>0$ and $x+y-1\ne0$, the function $s\mapsto R(x,s)$ is differentiable at $y$ with derivative
--   $$\frac{\partial R}{\partial y}(x,y)=\frac{\Big(\dfrac1{y^2}-\dfrac1x\Big)(x+y-1)-\Big(2-\dfrac yx-\dfrac1y\Big)}{(x+y-1)^2}.$$
--
--   This is a calculus step used, together with the derivative in $x$, to write the first-order conditions at an interior maximum of $R$ (inequality (15)).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L107-L122 (`ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_snd`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.hasDerivAt_twoEdgeRatio_snd {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun s => twoEdgeRatio x s)
      (((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) y := by sorry
