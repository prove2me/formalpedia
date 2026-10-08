-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_p73_retailer_bias
-- name    : CachonCoord.BaseStock.p73_retailer_bias
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:27.70853+00:00
-- url     : https://prove2.me/theorems/d18c72b0-6c83-4a69-8373-884aa1b6735d
-- title:
--   §6.7.1, p. 73 — the uncontracted retailer stocks below the channel optimum
-- statement:
--   Without a coordinating transfer, the retailer's cost is strictly convex on nonnegative stock levels. Let $s_r^*$ be its unique cost-minimizing base-stock level and $s_r^\circ$ the channel's unique cost-minimizing level. Both levels are positive, and
--   $$F_r(s_r^*)=\frac{\beta_r}{h_r+\beta_r},\qquad F_r(s_r^\circ)=\frac{\beta_r+\beta_s}{h_r+\beta_r+\beta_s},\qquad s_r^*<s_r^\circ.$$
--
--   The strict inequality is the stock-level distortion that the supplier-to-retailer transfer corrects.
--
--   **Formalization Note** The comparison uses the section's strict positivity of $\beta_s$. Both minimizers are unique over all real levels; the demand support and $F_r(0)=0$ make them positive.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, paragraph after Eq. (31), p. 73

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, p. 73, paragraph after (31): without a contract,
the retailer's unique optimum is below the channel's unique optimum. -/
theorem p73_retailer_bias (M : Model) :
    StrictConvexOn ℝ (Set.Ici 0) M.retailerCost ∧
    ∃ sr so : ℝ, 0 < sr ∧ sr < so ∧
      M.F sr = M.br / (M.hr + M.br) ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.retailerCost Set.univ sr ∧
      IsMinOn M.chainCost Set.univ so ∧
      (∀ s : ℝ, IsMinOn M.retailerCost Set.univ s → s = sr) ∧
      (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) := by sorry

end CachonCoord.BaseStock
