-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_attained
-- name    : ActuarialValuation.crRisk_attained
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:08.643975+00:00
-- url     : https://prove2.me/theorems/ea66b65c-8d33-43d1-81d5-6c81ad1e884f
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_attained
-- statement:
--   The robust premium is genuinely realised by one of the two candidate probability distributions.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_attained
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crWorstCaseDistribution
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crRisk_attained {n : ℕ} (p q X : Fin n→ℝ) : crScenarioRisk p q X = crExpected (crWorstCaseDistribution p q X) X := by sorry

end ActuarialValuation
