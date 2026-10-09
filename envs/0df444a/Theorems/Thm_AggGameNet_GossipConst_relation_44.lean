-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_relation_44
-- name    : AggGameNet.GossipConst.relation_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:48.535957+00:00
-- url     : https://prove2.me/theorems/3eaa6ce9-54e6-4225-bb8c-70df5e41bbd6
-- title:
--   Relation (44) — one-step coordinate disagreement
-- statement:
--   For a constant-step gossip run whose gradient evaluations are bounded by $C$, let $v^k(\ell)$ collect the $\ell$th coordinates of all agents' estimates and let $y^k$ be their mean. With $\alpha_{\max}=\max_i\alpha_i$, every trajectory, coordinate $\ell$ and tick $k$ satisfies
--
--   $$\|v^{k+1}(\ell)-[y^{k+1}]_\ell\mathbf1\|\le\|D(k)(v^k(\ell)-[y^k]_\ell\mathbf1)\|+\sqrt2\,C\alpha_{\max}.$$
--
--   This is the pathwise perturbation inequality used by Lemma 11. **Formalization Note** The paper obtains this sharper term from Lemma 9's proof because at most two agents update.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relation (44), proof of Lemma 11, p. 24

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

namespace AggGameNet.GossipConst

theorem relation_44 {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (I J : ℕ → Ω → Fin N) (alpha : Fin N → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v)
    (C : ℝ) (hC : ∀ ω i k,
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i)‖ ≤ C) :
    ∀ (ω : Ω) (ell : Fin n) (k : ℕ),
      ‖centeredCoord v (k+1) ω ell‖ ≤
        ‖Dk I J k ω (centeredCoord v k ω ell)‖ +
          Real.sqrt 2 * C * sSup (Set.range alpha) := by sorry

end AggGameNet.GossipConst
