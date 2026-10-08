-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_29
-- name    : CachonCoord.BaseStock.eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:45:49.524692+00:00
-- url     : https://prove2.me/theorems/783a600b-b353-49d2-a466-edff75a81ec2
-- title:
--   Eq. (29), p. 72 — expected backorders equal mean demand minus stock plus expected inventory
-- statement:
--   Let $D_r$ be nonnegative lead-time demand with finite mean $\mu_r$. Expected inventory and expected backorders at a real stock level $y$ are $I_r(y)=\mathbb E[(y-D_r)^+]$ and $B_r(y)=\mathbb E[(D_r-y)^+]$. Then
--   $$B_r(y)=\mu_r-y+I_r(y).$$
--
--   The identity connects the two shortfall functions and rewrites inventory costs in terms of $I_r$ alone.
--
--   **Formalization Note** The model requires the mean of $D_r$ to be integrable, avoiding the default value of a nonintegrable real integral. The identity holds at negative stock levels as well.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (29), p. 72

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (29), p. 72: the expected backorders
equal mean demand minus the stock level plus expected inventory. -/
theorem eq_29 (M : Model) :
    ∀ y : ℝ, M.B y = M.meanDemand - y + M.I y := by sorry

end CachonCoord.BaseStock
