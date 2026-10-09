-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_relation_55_equal
-- name    : AggGameNet.GossipConst.relation_55_equal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:46.491996+00:00
-- url     : https://prove2.me/theorems/1504141e-0868-4cff-a721-a7600d6c6235
-- title:
--   Relation (55), equal case — expected error recursion
-- statement:
--   In the equal-probability and equal-step case, let $x^*$ solve $\operatorname{VI}(K,\phi)$, and set $B=(\max_i\bar L_i)NM$ and $q=1-2\mu p\alpha$. Under Proposition 4's assumptions, for each $k\ge0$,
--
--   $$\mathbb E\|x^{k+1}-x^*\|^2\le q\,\mathbb E\|x^k-x^*\|^2+4p\alpha^2C^2N+2p\alpha B\sum_j\mathbb E\|v_j^k-y^k\|.$$
--
--   This recurrence feeds the limiting error bound. **Formalization Note** The paper's general (55) uses an invalid replacement of signed terms by $p_{\min}$; equal update probabilities remove that step. $C$ also bounds $F_i$ at feasible aggregate arguments, as in Lemma 3.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relation (55), p. 28, case p_i ≡ p and α_i ≡ α

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

open MeasureTheory ProbabilityTheory Filter

namespace AggGameNet.GossipConst

theorem relation_55_equal {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : AggGameNet.Gossip.GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : AggGameNet.Gossip.GossipDraws P I J p)
    (L : Fin N → ℝ) (h8 : Assumption8 K F L)
    (mu : ℝ) (hmu : 0 < mu) (hsm : StronglyMonotone K F mu)
    (alpha : Fin N → ℝ) (halpha : ∀ i, 0 < alpha i)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v)
    (pp : ℝ) (hpeq : ∀ i, AggGameNet.Gossip.pbar p i = pp)
    (a : ℝ) (haeq : ∀ i, alpha i = a) (ha : a < 1 / (2 * mu * pp))
    (C : ℝ) (hCrun : ∀ ω i k,
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i)‖ ≤ C)
    (hCK : ∀ i, ∀ xi ∈ K i, ∀ u ∈ AggGameNet.Sync.Kbar K, ‖F i xi u‖ ≤ C)
    (M : ℝ) (hM : ∀ i, ∀ xi ∈ K i, ∀ zi ∈ K i, ‖xi - zi‖ ≤ M)
    (xs : Fin N → AggGameNet.Sync.E n) (hxs : AggGameNet.Gossip.IsVISol K F xs) :
    ∀ k,
      (∫⁻ ω, ENNReal.ofReal (∑ i, ‖x (k+1) ω i - xs i‖ ^ 2) ∂P) ≤
        ENNReal.ofReal (1 - 2 * mu * pp * a) *
          (∫⁻ ω, ENNReal.ofReal (∑ i, ‖x k ω i - xs i‖ ^ 2) ∂P) +
        ENNReal.ofReal (4 * pp * a ^ 2 * C ^ 2 * (N : ℝ)) +
        ENNReal.ofReal
          (2 * pp * a * (sSup (Set.range Lbar) * (N : ℝ) * M)) *
          ∑ j, ∫⁻ ω, ENNReal.ofReal ‖v k ω j - AggGameNet.Gossip.yavg v k ω‖ ∂P := by sorry

end AggGameNet.GossipConst
