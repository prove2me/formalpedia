-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_proposition1_linear_rebate_loss
-- name    : ChannelRebate.Quantity.proposition1_linear_rebate_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:53.975226+00:00
-- url     : https://prove2.me/theorems/53c4c811-2d2a-49ea-9096-fecbaac49835
-- title:
--   Proposition 1, p. 996 — if T = 0, channel coordination requires m* < 0
-- statement:
--   In the setting of the mission, let $0<c<w<p$, $s<c$, $u>0$, and let $\bar Q_0 > 0$ satisfy $\Phi(\bar Q_0) = (p-c)/(p-s)$. Consider the **linear rebate** $(w,u,0)$, i.e. the target rebate with target $T = 0$. If this contract achieves channel coordination, in the sense that $\bar Q_0$ is the retailer's unique optimal order,
--   $$
--   \arg\max_{Q\ge 0} r(Q\mid 0) = \{\bar Q_0\},
--   $$
--   then the manufacturer's profit at $\bar Q_0$ is negative:
--   $$
--   m^* = (w-c)\bar Q_0 - uE\min(\bar Q_0,\xi) < 0.
--   $$
--
--   A rebate paid on every unit sold cannot both coordinate the channel and leave the manufacturer a profit; this is the motivation for the target in Theorem 1.
--
--   **Formalization Note** The manufacturer's profit is $(w-c)Q - uE(\min(Q,\xi)-T)^+$ at $T=0$; since $\xi \ge 0$ almost surely, the rebate term equals $uE\min(Q,\xi)$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 996, Proposition 1; proof p. 1005

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Taylor (2002), Proposition 1, p. 996. If `T = 0` (a linear rebate), then channel
coordination requires `m* < 0`: whenever the retailer's unique optimal order under
`(w, u, 0)` is the integrated-channel quantity `Q̄₀`, the manufacturer's profit at `Q̄₀`
is negative. -/
theorem proposition1_linear_rebate_loss (p c s w u : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (D : Demand)
    (Qbar0 : ℝ) (hQbar0 : 0 < Qbar0) (hΦbar : Phi D Qbar0 = (p - c) / (p - s))
    (hcoord : optimalOrders (retailerProfit p s w u 0 D) = {Qbar0}) :
    manufProfit c w u 0 D Qbar0 < 0 := by sorry

end ChannelRebate.Quantity
