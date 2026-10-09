-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_relations_30_31
-- name    : AggGameNet.GossipConst.relations_30_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:37.287577+00:00
-- url     : https://prove2.me/theorems/aaecfbf9-8ad9-48fa-acfe-967afd43d959
-- title:
--   Relations (30)–(31) — gossip contraction
-- statement:
--   For a connected graph with positive contact probabilities on every edge and independent gossip draws, there is $\lambda\in(0,1)$ such that, for every tick $k$ and Euclidean vector $z\in\mathbb R^N$,
--
--   $$\mathbb E\|D(k)z\|^2\le\lambda\|z\|^2,\qquad \mathbb E\|D(k)z\|\le\sqrt\lambda\|z\|,$$
--
--   where $D(k)=W(k)-N^{-1}\mathbf1\mathbf1^\top$. These are the contraction estimates used for disagreement. **Formalization Note** Expectations are nonnegative extended-real integrals, avoiding default values of Bochner integrals; the finite-valued integrands are measurable.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relations (30)–(31), p. 18

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Gossip

open MeasureTheory ProbabilityTheory Filter

namespace AggGameNet.GossipConst

theorem relations_30_31 {N : ℕ} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : AggGameNet.Gossip.GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : AggGameNet.Gossip.GossipDraws P I J p) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ Contraction30 P I J lam ∧
      ∀ k (z : EuclideanSpace ℝ (Fin N)),
        (∫⁻ ω, ENNReal.ofReal ‖Dk I J k ω z‖ ∂P) ≤
          ENNReal.ofReal (Real.sqrt lam * ‖z‖) := by sorry

end AggGameNet.GossipConst
