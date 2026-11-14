-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_continuous
-- name    : ConsistentSubmodular.Shadow.LeftLaw.inv_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:41.148366+00:00
-- url     : https://prove2.me/theorems/53a4abe8-2872-414e-a076-66cc30496dca
-- title:
--   Continuity of the inverse $X=H^{-1}$ of the ramp function
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support: weights $p_j\ge0$ with $\sum_jp_j=1$ on points $\ell_j$, whose smallest support point is $\ell_{\min}$ (some point with positive weight lies at or below $\ell_{\min}$). Let $H(x)=\sum_jp_j\max(0,x-\ell_j)$ and let $X=H^{-1}:[0,\infty)\to[\ell_{\min},\infty)$ be its inverse, extended by $X(0)$ to negative arguments. Then $X$ is continuous on $\mathbb R$.
--
--   $H$ is continuous, convex, piecewise linear and strictly increasing on $[\ell_{\min},\infty)$ with $H(\ell_{\min})=0$, so its inverse is continuous. This is a basic regularity property used when integrating against $X$ in the shadow-chain argument.
--
--   **Formalization Note** The inverse is defined by `Function.invFunOn` of $H$ on $[\ell_{\min},\infty)$ evaluated at $\max(y,0)$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L208-L224 (`ConsistentSubmodular.Shadow.LeftLaw.inv_continuous`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.inv_continuous : Continuous L.inv := by sorry
