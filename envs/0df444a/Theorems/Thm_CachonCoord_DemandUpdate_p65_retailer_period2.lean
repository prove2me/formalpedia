-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p65_retailer_period2
-- name    : CachonCoord.DemandUpdate.p65_retailer_period2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:34.896935+00:00
-- url     : https://prove2.me/theorems/dfd52c8e-696e-4df8-b432-3a8143488416
-- title:
--   §6.6.1, p. 65 — with p − b = λp, w₂ − b = λc₂: π₂ = λ(Ω₂ − c₂q₁) + w₂q₁, so the contract coordinates period 2
-- statement:
--   Take buy back terms with $\lambda \in [0,1]$ and
--   $$p - b = \lambda p, \qquad w_2 - b = \lambda c_2 .$$
--   Then for all $q_1$, $\xi$ and $q_2$ the retailer's period-2 profit is
--   $$\pi_2(q_2\,|\,q_1,\xi) = \lambda\big(\Omega_2(q_2\,|\,q_1,\xi) - c_2 q_1\big) + w_2 q_1 .$$
--   Consequently every supply chain optimal period-2 order (maximizing $\Omega_2(\cdot\,|\,q_1,\xi)$ over $q_2 \ge q_1$) is optimal for the retailer. When $\lambda > 0$ every retailer optimal order is supply chain optimal. The contract coordinates the retailer's period-2 decision.
--
--   **Formalization Note** At $\lambda = 0$ the retailer's period-2 profit does not depend on $q_2$, so every order is optimal for him; the converse direction is therefore stated for $\lambda > 0$ only.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 65, the display after "With any of those contracts"

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 65 (the display after "With any of those contracts").
With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 − b = λc_2`, the retailer's period-2 profit is
`π_2(q_2|q_1, ξ) = λ(Ω_2(q_2|q_1, ξ) − c_2 q_1) + w_2 q_1`, so every supply chain optimal period-2
order (over `q_2 ≥ q_1`) is optimal for the retailer, and for `λ > 0` conversely: the contract
coordinates the retailer's period-2 decision. -/
theorem p65_retailer_period2 (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) := by sorry

end CachonCoord.DemandUpdate
