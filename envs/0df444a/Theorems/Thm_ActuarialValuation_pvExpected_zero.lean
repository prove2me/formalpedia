-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpected_zero
-- name    : ActuarialValuation.pvExpected_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:38.077464+00:00
-- url     : https://prove2.me/theorems/ff1a5887-f89c-440c-96cf-d4da64fa98f4
-- title:
--   Equivalence premiums and loss variance: pvExpected_zero
-- statement:
--   Any finite loss distribution has zero expected value for a zero random loss.
--
--   Mathematical relation:
--
--   $$
--   pvExpected\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpected_zero {n : ℕ} (p : Fin n → ℝ) : pvExpected p (fun _ => 0) = 0 := by sorry

end ActuarialValuation
