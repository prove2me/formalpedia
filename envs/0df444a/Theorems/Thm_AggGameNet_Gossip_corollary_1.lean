-- Prove2me | Theorems.Thm_AggGameNet_Gossip_corollary_1
-- name    : AggGameNet.Gossip.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:42.306007+00:00
-- url     : https://prove2.me/theorems/6c210bc5-c528-417a-bc5c-b99b0d2aade4
-- title:
--   Corollary 1, p. 17 — three almost-sure stepsize series converge
-- statement:
--   Under the connected gossip graph, positive contact probabilities, and independent tick-pair law, let $\alpha_{k,i}=1/\Gamma_k(i)$ and $p_i=N^{-1}(1+\sum_jp_{ji})$. For every agent $i$, with probability one,
--
--   $$
--   \sum_{k=1}^{\infty}\frac{\alpha_{k,i}}k<\infty,\qquad
--   \sum_{k=1}^{\infty}\alpha_{k,i}^2<\infty,\qquad
--   \sum_{k=1}^{\infty}\left|\alpha_{k,i}-\frac1{kp_i}\right|<\infty.
--   $$
--
--   These summability statements supply the error controls for the stochastic convergence argument.
--
--   **Formalization Note** Lean indexes each series by $m\ge0$ and evaluates the displayed term at $k=m+1$, exactly covering the paper's range $k\ge1$.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Corollary 1, p. 17

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

namespace AggGameNet.Gossip

theorem corollary_1 {N : ℕ} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : GossipDraws P I J p) :
    ∀ i : Fin N, ∀ᵐ ω ∂P,
      Summable (fun k : ℕ => alphaG I J (k + 1) ω i / ((k + 1 : ℕ) : ℝ)) ∧
      Summable (fun k : ℕ => alphaG I J (k + 1) ω i ^ 2) ∧
      Summable (fun k : ℕ =>
        |alphaG I J (k + 1) ω i - 1 / (((k + 1 : ℕ) : ℝ) * pbar p i)|) := by sorry

end AggGameNet.Gossip
