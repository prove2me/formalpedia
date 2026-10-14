-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLossOrder_pointwise
-- name    : ActuarialValuation.crStopLossOrder_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:04.392186+00:00
-- url     : https://prove2.me/theorems/4cc51625-548f-4987-a905-aaec98294e0f
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossOrder_pointwise
-- statement:
--   Every pointwise larger loss schedule dominates the smaller in stop-loss order under common valid weights.
--
--   Mathematical relation:
--
--   $$
--   crStopLossOrder\_pointwise
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

namespace ActuarialValuation

theorem crStopLossOrder_pointwise {n : ℕ} (p X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crStopLossOrdered p X Y := by sorry

end ActuarialValuation
