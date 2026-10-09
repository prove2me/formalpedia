-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_lemma_11
-- name    : AggGameNet.GossipConst.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:03.760417+00:00
-- url     : https://prove2.me/theorems/e1571c9b-799f-43da-acf7-c326d3613b38
-- title:
--   Lemma 11 — limiting disagreement bounds
-- statement:
--   For a constant-step gossip run under Assumptions 1–3 and 7, let $C$ bound the gradient evaluations as in Lemma 3, and let $\lambda\in(0,1)$ satisfy (30). With $\alpha_{\max}=\max_i\alpha_i$ and $y^k=N^{-1}\sum_i v_i^k$,
--
--   $$\limsup_{k\to\infty}\sum_i\mathbb E\|v_i^k-y^k\|^2\le\frac{2n\alpha_{\max}^2C^2}{(1-\sqrt\lambda)^2},\qquad\limsup_{k\to\infty}\sum_i\mathbb E\|v_i^k-y^k\|\le\frac{\sqrt{2nN}\,\alpha_{\max}C}{1-\sqrt\lambda}.$$
--
--   These bounds quantify the persistent disagreement caused by constant steps. **Formalization Note** The final “a.s.” printed after the expectation display is treated as a slip. Expectations and limits are in extended nonnegative reals.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 11, pp. 24–26

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

open MeasureTheory ProbabilityTheory Filter

namespace AggGameNet.GossipConst

theorem lemma_11 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : AggGameNet.Gossip.GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : AggGameNet.Gossip.GossipDraws P I J p) (alpha : Fin N → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v)
    (C : ℝ) (hC : ∀ ω i k,
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i)‖ ≤ C)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (h30 : Contraction30 P I J lam) :
    Filter.limsup
      (fun k => ∑ i, ∫⁻ ω, ENNReal.ofReal (‖v k ω i - AggGameNet.Gossip.yavg v k ω‖ ^ 2) ∂P)
      atTop ≤
      ENNReal.ofReal
        (2 * (n : ℝ) * (sSup (Set.range alpha)) ^ 2 * C ^ 2 /
          (1 - Real.sqrt lam) ^ 2) ∧
    Filter.limsup
      (fun k => ∑ i, ∫⁻ ω, ENNReal.ofReal ‖v k ω i - AggGameNet.Gossip.yavg v k ω‖ ∂P)
      atTop ≤
      ENNReal.ofReal
        (Real.sqrt (2 * (n : ℝ) * (N : ℝ)) * sSup (Set.range alpha) * C /
          (1 - Real.sqrt lam)) := by sorry

end AggGameNet.GossipConst
