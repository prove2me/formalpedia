-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_symmetry
-- name    : ActuarialValuation.crRisk_symmetry
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:25.492198+00:00
-- url     : https://prove2.me/theorems/f4977b14-3b3a-412d-a920-03b089aac1d6
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_symmetry
-- statement:
--   Interchanging the two possible probability laws does not change the conservative premium.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_symmetry
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_symmetry {n : ℕ} (p q X : Fin n→ℝ) : crScenarioRisk p q X = crScenarioRisk q p X := by sorry

end ActuarialValuation
