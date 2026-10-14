-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_add
-- name    : ActuarialValuation.crExpected_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:31.581884+00:00
-- url     : https://prove2.me/theorems/09b0ba98-f6c9-470e-87b6-ebda75cf8b1a
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_add
-- statement:
--   Expected aggregate insurance losses add for dependent policies on a common outcome space.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_add
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_add {n : ℕ} (p X Y : Fin n→ℝ) : crExpected p (fun i=>X i+Y i) = crExpected p X+crExpected p Y := by sorry

end ActuarialValuation
