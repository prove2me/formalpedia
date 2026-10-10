-- Prove2me | Theorems.Thm_ActuarialValuation_frDiscount_positive
-- name    : ActuarialValuation.frDiscount_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:00.158609+00:00
-- url     : https://prove2.me/theorems/7f7e4218-963d-42d0-ae4c-3a3fc0370d3c
-- title:
--   Within-year survival and discount timing: frDiscount_positive
-- statement:
--   An exponentially discounted unit value is strictly positive at finite durations.
--
--   Mathematical relation:
--
--   $$
--   frDiscount\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount

namespace ActuarialValuation

theorem frDiscount_positive (delta t : ℝ) : 0 < frDiscount delta t := by sorry

end ActuarialValuation
