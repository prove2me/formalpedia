-- Prove2me | Theorems.Thm_DisruptReroute_Resil_zero_stock_cost
-- name    : DisruptReroute.Resil.zero_stock_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:35.978975+00:00
-- url     : https://prove2.me/theorems/d4b42e18-ee3a-4595-854d-cffabba3c7a6
-- title:
--   Proof of Theorem 5.1, EC p. 18 — equality at zero safety stock
-- statement:
--   For two tiered networks $A$ and $B$ that share prices, equity, holding costs, inverse supply curves, and tier assignments, suppose $B$ is more diversified than $A$. At zero safety stock and the same realization $c$ of net production costs, their aggregate switching and inventory costs agree:
--
--   $$\sum_i\zeta_i^A(0)=\sum_i\zeta_i^B(0).$$
--
--   This equality supplies the common denominator in the resilience ratio of Theorem 5.1.
--
--   **Formalization Note** Each network has its own computed fundamental-default set, which agrees under Definition 5.3. Zero safety stock is admissible in both networks.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), E-Companion, p. EC 18 (PDF 60), proof of Theorem 5.1, paragraph after displayed chain

import Mathlib
import Definitions.Def_DisruptReroute_Resil_Risk
import Definitions.Def_DisruptReroute_Resil_Diversification

namespace DisruptReroute.Resil

/-- Proof of Theorem 5.1, EC p. 18, equality at zero safety stock. -/
theorem zero_stock_cost {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (R : RiskData N M) (A B : OrderNetwork N M) (tier : Fin N → ℕ)
    (hA : IsTiered A tier) (hB : IsTiered B tier)
    (hDiv : MoreDiversified A B tier) (c : Fin N → ℝ) :
    (∑ i, zetaI R A c 0 i) = (∑ i, zetaI R B c 0 i) := by sorry

end DisruptReroute.Resil
