-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_two_scenario_nonlaw_invariant
-- name    : ActuarialValuation.crRisk_two_scenario_nonlaw_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:37.852024+00:00
-- url     : https://prove2.me/theorems/bc726820-760e-4142-97d2-e085bf33e893
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_two_scenario_nonlaw_invariant
-- statement:
--   Explicit two-point counterexample: equal distributions under one reference probability law can have different robust risk premia because the ambiguity set encodes scenario-level information.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_two\_scenario\_nonlaw\_invariant
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_two_scenario_nonlaw_invariant (p q X Y : Fin 2→ℝ) (hp : p 0=1/2 ∧ p 1=1/2) (hq : q 0=3/4 ∧ q 1=1/4) (hX : X 0=1 ∧ X 1=0) (hY : Y 0=0 ∧ Y 1=1) : crExpected p X=crExpected p Y ∧ crScenarioRisk p q X=3/4 ∧ crScenarioRisk p q Y=1/2 := by sorry

end ActuarialValuation
