-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_scale
-- name    : ActuarialValuation.crExpected_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:44.013156+00:00
-- url     : https://prove2.me/theorems/ad81c04f-5460-4a1b-9ed2-5a857cc40bd8
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_scale
-- statement:
--   Expected insurance loss is homogeneous under monetary rescaling.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_scale {n : ℕ} (p X : Fin n→ℝ) (c : ℝ) : crExpected p (fun i=>c*X i) = c*crExpected p X := by sorry

end ActuarialValuation
