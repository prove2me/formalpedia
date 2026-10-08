-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p66_retailer_period1
-- name    : CachonCoord.DemandUpdate.p66_retailer_period1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:37.073194+00:00
-- url     : https://prove2.me/theorems/1bb40aa0-3500-4b05-9c31-82c4c8106591
-- title:
--   §6.6.1, p. 66 — π₁(q₁) = −(w₁ − w₂ + λc₂)q₁ + λE[Ω₂], and π₁ = λΩ₁ when w₁ − w₂ + λc₂ = λc₁
-- statement:
--   Let $q_2(q_1,\xi)$ be a supply chain optimal period-2 order. Take a coordinating pair $\{w_2, b\}$: $\lambda \in [0,1]$, $p - b = \lambda p$ and $w_2 - b = \lambda c_2$. For every $q_1 \ge 0$ the retailer's period-1 expected profit is
--   $$\pi_1(q_1) = -(w_1 - w_2 + \lambda c_2)\,q_1 + \lambda E\big[\Omega_2(q_2(q_1,\xi)\,|\,q_1,\xi)\big].$$
--   If moreover $w_1$ is chosen so that
--   $$w_1 - w_2 + \lambda c_2 = \lambda c_1,$$
--   then
--   1. $\pi_1(q_1) = \lambda\,\Omega_1(q_1)$ for every $q_1 \ge 0$;
--   2. every supply chain optimal period-1 order $q_1 \ge 0$ is optimal for the retailer;
--   3. if $\lambda > 0$, every retailer optimal $q_1 \ge 0$ is supply chain optimal.
--
--   The retailer's optimal order equals the supply chain's, and the share $\lambda$ of the chain's profit goes to the retailer.
--
--   **Formalization Note** Optimality in $q_1$ is over $q_1 \ge 0$. At $\lambda = 0$ the retailer is indifferent among all orders, so the converse is stated for $\lambda > 0$.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 66, the displays of π₁(q₁), Ω₁(q₁) and π₁(q₁) = λΩ₁(q₁)

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 66 (the displays for `π_1`, `Ω_1` and `π_1 = λΩ_1`).
Let `q2sel` select a supply chain optimal period-2 order `q_2(q_1, ξ)`. With a coordinating
`{w_2, b}` pair (`λ ∈ [0, 1]`, `p − b = λp`, `w_2 − b = λc_2`), for every `q_1 ≥ 0`
1. `π_1(q_1) = −(w_1 − w_2 + λc_2)q_1 + λE[Ω_2(q_2(q_1, ξ)|q_1, ξ)]`;
2. if moreover `w_1 − w_2 + λc_2 = λc_1`, then `π_1(q_1) = λΩ_1(q_1)`;
and then every supply chain optimal `q_1 ≥ 0` is optimal for the retailer, and for `λ > 0`
conversely. -/
theorem p66_retailer_period1 (M : Model) (lam w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 =
      -(w1 - w2 + lam * M.c2) * q1 + lam * M.E (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ))) ∧
    (w1 - w2 + lam * M.c2 = lam * M.c1 →
      (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 = lam * M.Omega1 q2sel q1) ∧
      (∀ q1, 0 ≤ q1 → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1 →
        IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1) ∧
      (0 < lam → ∀ q1, 0 ≤ q1 → IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1 →
        IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1)) := by sorry

end CachonCoord.DemandUpdate
