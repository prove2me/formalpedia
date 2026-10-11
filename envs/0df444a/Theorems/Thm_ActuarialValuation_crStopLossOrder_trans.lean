-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLossOrder_trans
-- name    : ActuarialValuation.crStopLossOrder_trans
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:46.639+00:00
-- url     : https://prove2.me/theorems/d8e1e046-37b4-4817-8d28-ce76e7cdb80b
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossOrder_trans
-- statement:
--   Stop-loss risk order is transitive, allowing chained actuarial risk comparisons.
--
--   Mathematical relation:
--
--   $$
--   crStopLossOrder\_trans
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

namespace ActuarialValuation

theorem crStopLossOrder_trans {n : ℕ} (p X Y Z : Fin n→ℝ) (hXY : crStopLossOrdered p X Y) (hYZ : crStopLossOrdered p Y Z) : crStopLossOrdered p X Z := by sorry

end ActuarialValuation
