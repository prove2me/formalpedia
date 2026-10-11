-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_singleton
-- name    : ActuarialValuation.crRisk_singleton
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:35:39.569456+00:00
-- url     : https://prove2.me/theorems/b4ae0ecb-2375-4e35-bf84-ae25908f296f
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_singleton
-- statement:
--   Under a single candidate probability law, robust pricing reduces to expected loss.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_singleton
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

theorem crRisk_singleton {n : ℕ} (p X : Fin n→ℝ) : crScenarioRisk p p X = crExpected p X := by sorry

end ActuarialValuation
