-- Prove2me | Theorems.Thm_ActuarialValuation_crMargin_zero_same
-- name    : ActuarialValuation.crMargin_zero_same
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:37.529778+00:00
-- url     : https://prove2.me/theorems/b38e9d72-977e-4429-9513-ae2fc30876b4
-- title:
--   Actual finite loss distributions and scenario ambiguity: crMargin_zero_same
-- statement:
--   When both candidate distributions coincide, the ambiguity expected-loss spread vanishes.
--
--   Mathematical relation:
--
--   $$
--   crMargin\_zero\_same
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpectationMargin

namespace ActuarialValuation

theorem crMargin_zero_same {n : ℕ} (p X : Fin n→ℝ) : crExpectationMargin p p X=0 := by sorry

end ActuarialValuation
