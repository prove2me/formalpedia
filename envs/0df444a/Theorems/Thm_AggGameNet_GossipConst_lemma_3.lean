-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_lemma_3
-- name    : AggGameNet.GossipConst.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:34.025438+00:00
-- url     : https://prove2.me/theorems/a7a9c7b7-f2ae-4488-ab5c-1ff03f55e539
-- title:
--   Lemma 3 — uniform bounds for gradient evaluations
-- statement:
--   Under Assumptions 1 and 3 and the connected gossip setting, there is one finite constant $C$ such that, for every player, tick and trajectory,
--
--   $$\|F_i(x_i^k,Ny^k)\|\le C,\qquad\|F_i(x_i^k,N\hat v_i^k)\|\le C.$$
--
--   The common bound controls both gradient evaluations used in the later error estimates. **Formalization Note** Assumption 3 is extended to every aggregate argument, because $N\hat v_i^k$ need not belong to $\bar K$. The gossip matrix replaces the paper's bare column-sum condition; see the source's p. 10 footnote.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 3, p. 10, applied to gossip (26)–(29)

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

namespace AggGameNet.GossipConst

theorem lemma_3 {N n : ℕ} (hN : 0 < N) {Ω : Type*}
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : AggGameNet.Gossip.GossipProbs G p)
    (I J : ℕ → Ω → Fin N) (alpha : Fin N → ℝ)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J alpha x v) :
    ∃ C : ℝ, ∀ ω i k,
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.yavg v k ω)‖ ≤ C ∧
      ‖F i (x k ω i) ((N : ℝ) • AggGameNet.Gossip.vhat I J v k ω i)‖ ≤ C := by sorry

end AggGameNet.GossipConst
