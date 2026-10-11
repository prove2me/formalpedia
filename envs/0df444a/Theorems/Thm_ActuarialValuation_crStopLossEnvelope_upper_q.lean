-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLossEnvelope_upper_q
-- name    : ActuarialValuation.crStopLossEnvelope_upper_q
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:33.001473+00:00
-- url     : https://prove2.me/theorems/a2ea443c-1c6e-4843-a55f-514549a002b7
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLossEnvelope_upper_q
-- statement:
--   Worst-case stop-loss premium also covers the second candidate probability law.
--
--   Mathematical relation:
--
--   $$
--   crStopLossEnvelope\_upper\_q
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossEnvelope

namespace ActuarialValuation

theorem crStopLossEnvelope_upper_q {n : ℕ} (p q X : Fin n→ℝ) (d : ℝ) : crStopLoss q X d≤crStopLossEnvelope p q X d := by sorry

end ActuarialValuation
