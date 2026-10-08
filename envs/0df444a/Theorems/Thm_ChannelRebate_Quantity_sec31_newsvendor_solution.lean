-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_sec31_newsvendor_solution
-- name    : ChannelRebate.Quantity.sec31_newsvendor_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:50.335742+00:00
-- url     : https://prove2.me/theorems/f4d617f9-43ee-4aef-a1f2-1967f0eec53a
-- title:
--   §3.1, p. 995 — the channel orders Q̄₀ = Φ⁻¹((p−c)/(p−s)) and earns (p−s)Γ(Q̄₀); the wholesale-only retailer orders Q₀ < Q̄₀ and earns (p−s)Γ(Q₀)
-- statement:
--   Let demand $\xi$ have a density $\varphi$ that vanishes on $(-\infty,0)$ and is positive on $[0,\infty)$, with distribution $\Phi$ and $\Gamma(Q) = \int_0^Q \xi\,d\Phi(\xi)$. Let $0 < c < w < p$ and $s < c$. Let $\bar Q_0 > 0$ and $Q_0 > 0$ be the critical fractiles
--   $$
--   \Phi(\bar Q_0) = \frac{p-c}{p-s}, \qquad \Phi(Q_0) = \frac{p-w}{p-s}.
--   $$
--   Then:
--   1. $\bar Q_0$ is the unique maximizer over $Q \ge 0$ of the channel profit $\pi(Q) = -cQ + pE\min(Q,\xi) + sE(Q-\xi)^+$, and $\pi(\bar Q_0) = (p-s)\Gamma(\bar Q_0)$;
--   2. $Q_0$ is the unique maximizer over $Q \ge 0$ of the wholesale price-only retailer profit $-wQ + pE\min(Q,\xi) + sE(Q-\xi)^+$, and its value there is $\underline r = (p-s)\Gamma(Q_0)$;
--   3. $Q_0 < \bar Q_0$.
--
--   This is the integrated-channel benchmark $\pi = (p-s)\Gamma(\bar Q_0)$ that every coordination statement of the mission refers to, together with the double-marginalization gap $Q_0 < \bar Q_0$.
--
--   **Formalization Note** $\Phi^{-1}$ is never used as a function: each fractile is a hypothesis stating its defining equation. Optimality is maximization over $Q \ge 0$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 995, §3.1

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Taylor (2002), §3.1, p. 995. The integrated channel orders `Q̄₀ = Φ⁻¹((p − c)/(p − s))`
and earns `π = (p − s)Γ(Q̄₀)`; under a wholesale price-only contract the retailer orders
`Q₀ = Φ⁻¹((p − w)/(p − s))` and earns `r̲ = (p − s)Γ(Q₀)`; and `Q₀ < Q̄₀`.
The critical fractiles are given by their defining equations. -/
theorem sec31_newsvendor_solution (p c s w : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (D : Demand)
    (Qbar0 : ℝ) (hQbar0 : 0 < Qbar0) (hΦbar : Phi D Qbar0 = (p - c) / (p - s))
    (Q0 : ℝ) (hQ0 : 0 < Q0) (hΦ0 : Phi D Q0 = (p - w) / (p - s)) :
    optimalOrders (chainProfit p c s D) = {Qbar0} ∧
      chainProfit p c s D Qbar0 = (p - s) * Gam D Qbar0 ∧
      optimalOrders (wholesaleProfit p s w D) = {Q0} ∧
      wholesaleProfit p s w D Q0 = (p - s) * Gam D Q0 ∧
      Q0 < Qbar0 := by sorry

end ChannelRebate.Quantity
