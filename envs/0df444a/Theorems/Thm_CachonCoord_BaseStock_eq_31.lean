-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_31
-- name    : CachonCoord.BaseStock.eq_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:57.752168+00:00
-- url     : https://prove2.me/theorems/b5f8637a-d69c-46b5-8d5c-17a4f823c0c3
-- title:
--   Eq. (31), p. 73 — the channel's unique optimal base-stock level
-- statement:
--   Let $c(s)$ be the total cost in the single-location base-stock model, $F_r$ the cdf of nonnegative lead-time demand, and $\beta=\beta_r+\beta_s$. There is one channel-optimal stock level $s_r^\circ>0$. It minimizes $c$ over all real stock levels and satisfies
--   $$I_r'(s_r^\circ)=F_r(s_r^\circ)=\frac{\beta}{h_r+\beta}.$$
--
--   The critical ratio identifies the stock level that the contract in (33) must induce the retailer to choose.
--
--   **Formalization Note** Uniqueness is stated among all real minimizers, including negative stock levels. The positivity of the cost rates and $F_r(0)=0$ place the critical ratio strictly inside $(0,1)$ and make the optimum positive.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (31), p. 73

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (31), p. 73: the unique channel-optimal
base-stock level is positive and satisfies the critical fractile equation. -/
theorem eq_31 (M : Model) :
    ∃ so : ℝ, 0 < so ∧ HasDerivAt M.I (M.F so) so ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.chainCost Set.univ so ∧
      ∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so := by sorry

end CachonCoord.BaseStock
