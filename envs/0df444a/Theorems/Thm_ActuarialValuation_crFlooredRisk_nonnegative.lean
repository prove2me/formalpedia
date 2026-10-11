-- Prove2me | Theorems.Thm_ActuarialValuation_crFlooredRisk_nonnegative
-- name    : ActuarialValuation.crFlooredRisk_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:42.910973+00:00
-- url     : https://prove2.me/theorems/b8bd898e-bab8-4858-bd82-5ea7192dd7cc
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crFlooredRisk_nonnegative
-- statement:
--   Floored capital requirement is always nonnegative, regardless of actual insured gains.
--
--   Mathematical relation:
--
--   $$
--   crFlooredRisk\_nonnegative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crFlooredRisk

namespace ActuarialValuation

theorem crFlooredRisk_nonnegative {n : ℕ} (p q X : Fin n→ℝ) : 0≤crFlooredRisk p q X := by sorry

end ActuarialValuation
