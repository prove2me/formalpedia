-- Prove2me | Theorems.Thm_DisruptReroute_Resil_theorem_5_1
-- name    : DisruptReroute.Resil.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:39.466686+00:00
-- url     : https://prove2.me/theorems/118c8c0b-8563-4cc9-a0bd-88ebea2a0d27
-- title:
--   Theorem 5.1 — a more diversified tiered network is more resilient
-- statement:
--   Let $A$ and $B$ be tiered supply chain networks on the same positive numbers of firms and goods. They have the same prices, initial equity, holding costs, inverse supply curves, and tier assignment, and differ only in their order profiles. If $B$ is more diversified than $A$ in the sense of Definition 5.3, then for every common realization $c$ of net production costs and every uniform safety stock $\theta$ satisfying Assumption 2.1 in both networks,
--
--   $$\zeta^A(\theta)\le\zeta^B(\theta).$$
--
--   Thus diversification cannot reduce the percentage of out-of-stock loss offset by safety stock.
--
--   **Formalization Note** The paper states an almost-sure comparison; its proof is pointwise in the common cost realization, and the Lean statement uses that stronger form. Fundamental defaults are computed independently for each network. The ratio is zero when its baseline-cost denominator is zero.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), p. 27, Theorem 5.1; E-Companion, pp. EC 18–19, proof

import Mathlib
import Definitions.Def_DisruptReroute_Resil_Risk
import Definitions.Def_DisruptReroute_Resil_Diversification

namespace DisruptReroute.Resil

/-- Theorem 5.1: diversification increases resilience in tiered networks. -/
theorem theorem_5_1 {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (R : RiskData N M) (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier)
    (hDiv : MoreDiversified A B tier) :
    MoreResilient R B A tier := by sorry

end DisruptReroute.Resil
