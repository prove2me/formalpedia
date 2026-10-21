-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_theorem_2
-- name    : DeferredInspection.SingleAgent.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:14.628154+00:00
-- url     : https://prove2.me/theorems/a1674368-5ff2-4c49-90dd-3578f8c6244d
-- title:
--   Theorem 2, p. 12 — the explicit single-agent auction is globally optimal
-- statement:
--   Suppose the buyer's value has density $f$ satisfying Assumption 1. Define $G(t)=\int_0^t yf(y)\,dy$. There exist lower and upper thresholds $\underline v,\bar v$ satisfying $\bar v=b(1)$ and the allocation's integral branch reaching one at $\bar v$. For every such pair, use
--
--   $$b(v)=\begin{cases}0,&v\le\underline v,\\G^{-1}(G(v)-G(\underline v)),&v>\underline v,\end{cases}\qquad
--   x(v)=\begin{cases}\displaystyle\int_{\underline v}^{b^{-1}(v)}
--   \frac{b'(t)}{t}\,dt,&v<\bar v,\\1,&v\ge\bar v,\end{cases}$$
--
--   together with the paper's three-branch payment rule. The resulting $(x,p)$ is feasible and maximizes expected payment $\int_0^1p(v)f(v)\,dv$ among **all** feasible deferred-inspection mechanisms satisfying (8) and (9).
--
--   **Formalization Note** The feasibility class requires integrability of $pf$. IC uses the forfeited report $w$ in the deviation payoff $v x(w)-w$. The boundary equation uses the integral branch at $\bar v$, and threshold existence is asserted separately, so optimality is not vacuous.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 12, Theorem 2 and (15)

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem theorem_2 (f : ℝ → ℝ) (hf : Assumption1 f) :
    (∃ vl vh, BoundaryConds f vl vh) ∧
    ∀ vl vh, BoundaryConds f vl vh →
      IsOptimal f (optAlloc f vl vh) (optPayment f vl vh) := by sorry

end DeferredInspection.SingleAgent
