-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLossOrder_refl
-- name    : ActuarialValuation.crStopLossOrder_refl
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:32.451304+00:00
-- url     : https://prove2.me/theorems/02e5b240-b6ba-4b56-a2e3-dc67c4a827ab
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossOrder_refl
-- statement:
--   An insurance loss distribution is in stop-loss order with itself.
--
--   Mathematical relation:
--
--   $$
--   crStopLossOrder\_refl
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossOrdered

namespace ActuarialValuation

theorem crStopLossOrder_refl {n : ℕ} (p X : Fin n→ℝ) : crStopLossOrdered p X X := by sorry

end ActuarialValuation
