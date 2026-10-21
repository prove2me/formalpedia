-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_lemma_2
-- name    : DeferredInspection.SingleAgent.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:16.567041+00:00
-- url     : https://prove2.me/theorems/42158c2f-2b75-4760-a539-6a8447423cd8
-- title:
--   Lemma 2, p. 10 — smooth strictly concave approximation with convergent revenue
-- statement:
--   For a continuous concave allocation rule $x:V\to[0,1]$, there are allocation rules $x_k$ and thresholds $\bar v_k\in V$ such that each $x_k$ is differentiable and strictly concave on $[0,\bar v_k]$, equals one for $v>\bar v_k$, converges uniformly to $x$, and has revenue converging to that of $x$:
--
--   $$\sup_{v\in V}|x_k(v)-x(v)|\longrightarrow0,\qquad
--   R_f(x_k)\longrightarrow R_f(x).$$
--
--   Here $R_f$ uses the optimal payment rule (10) and the value density $f$ from Assumption 1. The result supports passage to the SCD class.
--
--   **Formalization Note** Each approximant has its own threshold. The source says $v>\bar v_k$ in this lemma; its separate SCD definition includes the boundary.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 10, Lemma 2; proof pp. 29–30

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem lemma_2 (f : ℝ → ℝ) (hf : Assumption1 f) (x : ℝ → ℝ)
    (hx : IsAllocation x) (hc : ContinuousOn x (Icc 0 1))
    (hcv : ConcaveOn ℝ (Icc 0 1) x) :
    ∃ (xs : ℕ → ℝ → ℝ) (vh : ℕ → ℝ),
      (∀ k, IsAllocation (xs k) ∧ vh k ∈ Icc (0 : ℝ) 1 ∧
        StrictConcaveOn ℝ (Icc 0 (vh k)) (xs k) ∧
        DifferentiableOn ℝ (xs k) (Icc 0 (vh k)) ∧
        ∀ v ∈ Ioc (vh k) 1, xs k v = 1) ∧
      TendstoUniformlyOn xs x atTop (Icc 0 1) ∧
      Tendsto (fun k => allocRevenue f (xs k)) atTop (𝓝 (allocRevenue f x)) := by sorry

end DeferredInspection.SingleAgent
