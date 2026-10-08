-- Prove2me | Theorems.Thm_DisruptReroute_Resil_diversified_cost_inequality
-- name    : DisruptReroute.Resil.diversified_cost_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:45.005122+00:00
-- url     : https://prove2.me/theorems/ea807632-86dd-4d5a-a626-3743fd5421da
-- title:
--   Proof of Theorem 5.1, EC p. 18 — diversification lowers total cost
-- statement:
--   Let $A$ and $B$ be tiered networks on the same positive numbers of firms and goods, sharing prices, equity, holding costs, inverse supply curves, and tier assignments. Suppose $B$ is more diversified than $A$ in the sense of Definition 5.3. For a common realization $c$ of net production costs and a uniform safety stock $\theta$ satisfying Assumption 2.1 in both networks,
--
--   $$\sum_i\zeta_i^B(\theta)\le\sum_i\zeta_i^A(\theta).$$
--
--   This is the inequality step of the displayed chain in the proof of Theorem 5.1.
--
--   **Formalization Note** Each network computes its own fundamental-default set; equality of these sets follows from the diversification conditions. The comparison retains all holding costs in both networks and uses the corrected supplier-good index of Definition 5.3.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), E-Companion, p. EC 18 (PDF 60), proof of Theorem 5.1, inequality line

import Mathlib
import Definitions.Def_DisruptReroute_Resil_Risk
import Definitions.Def_DisruptReroute_Resil_Diversification

namespace DisruptReroute.Resil

/-- Proof of Theorem 5.1, EC p. 18, the inequality in the displayed chain. -/
theorem diversified_cost_inequality {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (R : RiskData N M) (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier)
    (hDiv : MoreDiversified A B tier) (c : Fin N → ℝ) (θ : ℝ)
    (hθA : AssumptionTwoOne A tier θ) (hθB : AssumptionTwoOne B tier θ) :
    (∑ i, zetaI R B c θ i) ≤ (∑ i, zetaI R A c θ i) := by sorry

end DisruptReroute.Resil
