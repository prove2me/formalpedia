-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_p75_transfer_decomposition
-- name    : CachonCoord.BaseStock.p75_transfer_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:55:47.930115+00:00
-- url     : https://prove2.me/theorems/c022516b-da77-4631-9ed9-f14cd1ff9fec
-- title:
--   §6.7.1, p. 75 — t_I I_r(y) + t_B B_r(y) = (t_I + t_B) I_r(y) + t_B(μ_r − y)
-- statement:
--   In the single-location base-stock model, let $I_r(y)$ and $B_r(y)$ be the retailer's expected inventory and expected backorders at inventory level $y$, and $\mu_r$ the mean lead-time demand. For all constant transfer rates $t_I,t_B$ and every real $y$,
--   $$t_I I_r(y)+t_B B_r(y)=(t_I+t_B)I_r(y)+t_B(\mu_r-y).$$
--
--   The decomposition shows that $t_B$ acts as the parameter that affects the payment linearly in the retailer's action, and $t_I+t_B$ as the parameter that acts through the distribution-dependent function $I_r$, as the wholesale price and the buy-back rate do in a buy-back contract.
--
--   **Formalization Note** Positive transfers are payments from the supplier to the retailer, as on p. 73.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, display on p. 75

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 75: for any constant rates `t_I`, `t_B` (positive meaning a
payment from the supplier to the retailer) and any inventory level `y`,
`t_I I_r(y) + t_B B_r(y) = (t_I + t_B) I_r(y) + t_B (μ_r - y)`. -/
theorem p75_transfer_decomposition (M : Model) :
    ∀ tI tB y : ℝ,
      tI * M.I y + tB * M.B y = (tI + tB) * M.I y + tB * (M.meanDemand - y) := by sorry

end CachonCoord.BaseStock
