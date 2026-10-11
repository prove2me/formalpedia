-- Prove2me | Theorems.Thm_ActuarialValuation_crLoading_nonnegative
-- name    : ActuarialValuation.crLoading_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:27.840645+00:00
-- url     : https://prove2.me/theorems/098c5e08-bb8d-4031-a8ff-924eb2030fab
-- title:
--   Coherent worst-case actuarial premium and portfolio: crLoading_nonnegative
-- statement:
--   The robust premium loading relative to first-law expectation cannot be negative.
--
--   Mathematical relation:
--
--   $$
--   crLoading\_nonnegative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crLoading

namespace ActuarialValuation

theorem crLoading_nonnegative {n : ℕ} (p q X : Fin n→ℝ) : 0≤crLoading p q X := by sorry

end ActuarialValuation
