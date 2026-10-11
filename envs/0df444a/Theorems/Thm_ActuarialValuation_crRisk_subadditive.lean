-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_subadditive
-- name    : ActuarialValuation.crRisk_subadditive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:36:40.712968+00:00
-- url     : https://prove2.me/theorems/ebcd2ebc-dbe4-48cb-abac-74b116e82e53
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_subadditive
-- statement:
--   The maximum of two linear expected-loss premiums is subadditive for joint portfolio losses, without independence assumptions.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_subadditive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_subadditive {n : ℕ} (p q X Y : Fin n→ℝ) : crScenarioRisk p q (fun i=>X i+Y i) ≤ crScenarioRisk p q X+crScenarioRisk p q Y := by sorry

end ActuarialValuation
