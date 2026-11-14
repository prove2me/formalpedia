-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_twoEdgeRatio_critical
-- name    : ConsistentSubmodular.Chains.twoEdgeRatio_critical
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:59.092127+00:00
-- url     : https://prove2.me/theorems/63f758cb-de77-4b0d-80ca-0025c44fe364
-- title:
--   First-order conditions for $R(x,y)$: $\Phi(y/x)=0$ and $R=u^3(1+u)$
-- statement:
--   Let $R(x,y)=\dfrac{2-y/x-1/y}{x+y-1}$ and let $1<y<x$ be such that both partial derivatives of $R$ vanish at $(x,y)$:
--   $$\frac{\frac{y}{x^2}(x+y-1)-(2-\frac yx-\frac1y)}{(x+y-1)^2}=0,\qquad \frac{(\frac1{y^2}-\frac1x)(x+y-1)-(2-\frac yx-\frac1y)}{(x+y-1)^2}=0 .$$
--   Then, with $u=y/x$,
--
--   1. $\Phi(u)=u^4+u^3-2u^2-3u+2=0$;
--   2. $R(x,y)=y/x^2$;
--   3. $R(x,y)=u^3(1+u)=(y/x)^3\,(1+y/x)$.
--
--   With $v=1/x$, the first-order conditions give $v=u^2(1+u)$ and $\Phi(u)=0$, so that $R(x,y)=y/x^2=uv=u^3(1+u)$. This identifies the value of $R$ at an interior critical point as the constant $q$ (via $q=u_1^3(1+u_1)$).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L124-L176 (`ConsistentSubmodular.Chains.twoEdgeRatio_critical`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.twoEdgeRatio_critical {x y : ℝ} (hy : 1 < y) (hyx : y < x)
    (hfx : (y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0)
    (hfy : ((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0) :
    phi (y / x) = 0 ∧ twoEdgeRatio x y = y / x ^ 2 ∧
      twoEdgeRatio x y = (y / x) ^ 3 * (1 + y / x) := by sorry
