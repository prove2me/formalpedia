-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_lemma_2
-- name    : AggGameNet.GossipConst.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:26.301981+00:00
-- url     : https://prove2.me/theorems/5c5dbb21-9393-4e05-afdf-afe24100eb23
-- title:
--   Lemma 2 — average tracking identity
-- statement:
--   For a gossip run with $N\ge1$, let $y^k=N^{-1}\sum_i v_i^k$ be the mean of the agents' estimates. Then at every tick and on every trajectory,
--
--   $$y^k=\frac1N\sum_i x_i^k.$$
--
--   This identity identifies the common estimate mean with the true average decision. **Formalization Note** The column-stochastic hypothesis printed in Lemma 2 is automatic for the gossip matrices (26).
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 2, p. 10, applied to (26)–(29)

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

namespace AggGameNet.GossipConst

theorem lemma_2 {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (I J : ℕ → Ω → Fin N) (alpha : Fin N → ℝ)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v) :
    ∀ k ω, AggGameNet.Gossip.yavg v k ω = (1 / (N : ℝ)) • ∑ i, x k ω i := by sorry

end AggGameNet.GossipConst
