-- Prove2me | Theorems.Thm_DisruptReroute_Resil_tier_grouped_cost
-- name    : DisruptReroute.Resil.tier_grouped_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:21.138551+00:00
-- url     : https://prove2.me/theorems/48df23a6-fa8e-49f2-94ba-736d62a1d53f
-- title:
--   Proof of Theorem 5.1, EC p. 18 — tier-grouped cost identity
-- statement:
--   Consider a tiered supply chain with positive numbers of firms and goods, common cost realization $c$, and nonnegative uniform safety stock $\theta$ no larger than each actual supplier order. For each good $m$, let $L_m$ be the buyers of firms that fundamentally default, and put $T_m=\sum_{i\in L_m}\sum_{k\in D_0(\theta)}o^m_{ki}-|L_m|\theta$. Then
--
--   $$\sum_i\zeta_i(\theta)=\sum_i\sum_{m=1}^{M}\theta\lambda_i^m+\sum_{m=1}^{M}T_m s_m^{-1}(T_m).$$
--
--   The identity groups switching costs by good. It is the first part of the displayed chain in the proof of Theorem 5.1.
--
--   **Formalization Note** The printed chain keeps only each firm's input-good holding cost; the definition of $\zeta_i$ on p. 25 includes all goods. The full holding-cost sum is retained here. Goods and tiers are one-based.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), E-Companion, p. EC 18 (PDF 60), proof of Theorem 5.1, first three lines of displayed chain

import Mathlib
import Definitions.Def_DisruptReroute_Resil_Risk

namespace DisruptReroute.Resil

/-- Proof of Theorem 5.1, EC p. 18, first three lines, with all holding costs retained. -/
theorem tier_grouped_cost {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (R : RiskData N M) (O : OrderNetwork N M) (tier : Fin N → ℕ)
    (hTier : IsTiered O tier) (c : Fin N → ℝ) (θ : ℝ)
    (hθ : AssumptionTwoOne O tier θ) :
    (∑ i, zetaI R O c θ i) = groupedCost R O c θ := by sorry

end DisruptReroute.Resil
