-- Prove2me | Theorems.Thm_AggGameNet_Gossip_proposition_3
-- name    : AggGameNet.Gossip.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:51.340296+00:00
-- url     : https://prove2.me/theorems/55d84e3f-c3b5-43c1-b0d5-7a2f5999ee5e
-- title:
--   Proposition 3, p. 21 — diminishing-step gossip converges almost surely
-- statement:
--   Consider $N\ge1$ players with nonempty compact convex strategy sets $K_i$. Their continuous game map $\phi_i(x)=F_i(x_i,\sum_jx_j)$ is strictly monotone on $K=\prod_iK_i$, and every $F_i(x_i,\cdot)$ has a positive uniform Lipschitz bound. On a connected undirected graph, every waking agent contacts each neighbour with positive probability. Tick pairs $(I^k,J^k)$ are independent, with $\Pr(I^k=i,J^k=j)=p_{ij}/N$. From a fixed feasible initial profile, the two selected agents at each tick average their estimates and take the projected step with $\alpha_{k,i}=1/\Gamma_k(i)$. Then there is a unique solution $x^*$ of $\mathrm{VI}(K,\phi)$ and
--
--   $$
--   x^k\longrightarrow x^*\quad\text{almost surely}.
--   $$
--
--   Under the paper's convex payoff model, this $x^*$ is the unique Nash equilibrium. The result certifies equilibrium computation using only pairwise random communication and agent-specific update counts.
--
--   **Formalization Note** The Poisson clocks are represented by their discrete tick-pair law. Initial decisions are deterministic. The Lipschitz condition is extended to all aggregate arguments because the algorithm can evaluate $F_i$ outside the aggregate feasible set; this necessary repair of the printed domain is disclosed in the mission description.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Proposition 3, p. 21

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace AggGameNet.Gossip

theorem proposition_3 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (h2 : AggGameNet.Sync.Assumption2 K F)
    (Lbar : Fin N → ℝ) (h3 : AggGameNet.Sync.Assumption3 K F Lbar)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : GossipProbs G p)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (I J : ℕ → Ω → Fin N)
    (hdraw : GossipDraws P I J p)
    (x₀ : Fin N → AggGameNet.Sync.E n) (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (hrun : IsGossipRun K F I J x₀ x v) :
    ∃ xs : Fin N → AggGameNet.Sync.E n, IsVISol K F xs ∧
      (∀ y : Fin N → AggGameNet.Sync.E n, IsVISol K F y → y = xs) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => x k ω) atTop (𝓝 xs) := by sorry

end AggGameNet.Gossip
