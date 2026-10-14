-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_positive_homogeneous
-- name    : ActuarialValuation.crRisk_positive_homogeneous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:08.964018+00:00
-- url     : https://prove2.me/theorems/68d79942-82a2-4943-baa5-cdb320741876
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_positive_homogeneous
-- statement:
--   Worst-case expected loss scales by any nonnegative monetary multiple.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_positive\_homogeneous
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_positive_homogeneous {n : ℕ} (p q X : Fin n→ℝ) (c : ℝ) (hc : 0≤c) : crScenarioRisk p q (fun i=>c*X i) = c*crScenarioRisk p q X := by sorry

end ActuarialValuation
