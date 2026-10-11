-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_at_least_q
-- name    : ActuarialValuation.crRisk_at_least_q
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:09.549117+00:00
-- url     : https://prove2.me/theorems/97b500a8-e722-4a2c-9270-a0e4cd82f44d
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_at_least_q
-- statement:
--   Robust premium cannot fall below the second candidate-law equivalence premium.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_at\_least\_q
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crRisk_at_least_q {n : ℕ} (p q X : Fin n→ℝ) : crExpected q X≤crScenarioRisk p q X := by sorry

end ActuarialValuation
