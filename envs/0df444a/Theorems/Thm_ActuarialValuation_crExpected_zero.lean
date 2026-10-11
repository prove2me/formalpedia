-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_zero
-- name    : ActuarialValuation.crExpected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:14.585982+00:00
-- url     : https://prove2.me/theorems/cc4b93df-a590-4c28-bdd7-009fdd497476
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_zero
-- statement:
--   Zero portfolio loss produces zero expected outgo under any weights.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_zero {n : ℕ} (p : Fin n→ℝ) : crExpected p (fun _ => 0) = 0 := by sorry

end ActuarialValuation
