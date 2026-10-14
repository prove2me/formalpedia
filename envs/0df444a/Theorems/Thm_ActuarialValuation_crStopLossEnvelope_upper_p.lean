-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLossEnvelope_upper_p
-- name    : ActuarialValuation.crStopLossEnvelope_upper_p
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:20.266978+00:00
-- url     : https://prove2.me/theorems/8f67fe9a-b7a7-4e0f-b962-70159b5b90d6
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossEnvelope_upper_p
-- statement:
--   Worst-case expected stop loss upper-bounds the original probability scenario's stop-loss value.
--
--   Mathematical relation:
--
--   $$
--   crStopLossEnvelope\_upper\_p
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossEnvelope

namespace ActuarialValuation

theorem crStopLossEnvelope_upper_p {n : ℕ} (p q X : Fin n→ℝ) (d : ℝ) : crStopLoss p X d≤crStopLossEnvelope p q X d := by sorry

end ActuarialValuation
