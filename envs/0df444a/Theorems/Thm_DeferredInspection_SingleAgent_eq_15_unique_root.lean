-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_eq_15_unique_root
-- name    : DeferredInspection.SingleAgent.eq_15_unique_root
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:22.337596+00:00
-- url     : https://prove2.me/theorems/c9448f3d-9e78-4078-8524-7f5a26cba452
-- title:
--   Equation (15), p. 12 — unique lower threshold and threshold order
-- statement:
--   For a density $f$ satisfying Assumption 1, the threshold equation (15) has exactly one solution $\underline v\in(0,1)$:
--
--   $$\int_{\underline v}^{1}
--     \frac{f(t)}
--     {G^{-1}(G(t)-G(\underline v))\,
--      f(G^{-1}(G(t)-G(\underline v)))}\,dt=1.$$
--
--   At this solution, $\underline v\le b(1)$, so the lower threshold does not exceed the upper threshold $\bar v=b(1)$. The equation fixes the remaining parameter of Theorem 2's auction.
--
--   **Formalization Note** The value of the integrand at $t=\underline v$ is immaterial to the integral. The expression is integrable despite its inverse-square-root singularity at this endpoint.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 12, (15) and Theorem 2

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem eq_15_unique_root (f : ℝ → ℝ) (hf : Assumption1 f) :
    (∃! vl, vl ∈ Ioo (0 : ℝ) 1 ∧
      ∫ t in vl..1,
        f t / (Ginv f (G f t - G f vl) *
          f (Ginv f (G f t - G f vl))) = 1) ∧
    ∀ vl ∈ Ioo (0 : ℝ) 1,
      (∫ t in vl..1,
        f t / (Ginv f (G f t - G f vl) *
          f (Ginv f (G f t - G f vl)))) = 1 →
      vl ≤ bidFn f vl 1 := by sorry

end DeferredInspection.SingleAgent
