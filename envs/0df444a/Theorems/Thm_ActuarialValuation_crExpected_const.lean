-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_const
-- name    : ActuarialValuation.crExpected_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:00.544176+00:00
-- url     : https://prove2.me/theorems/eecc7105-6a23-4a35-9b38-01a5859fc900
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_const
-- statement:
--   Expectations of deterministic loss amounts equal the loss when probability weights sum to one.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_const {n : ℕ} (p : Fin n→ℝ) (c : ℝ) (hn : (∑ i : Fin n,p i)=1) : crExpected p (fun _=>c)=c := by sorry

end ActuarialValuation
