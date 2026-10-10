-- Prove2me | Theorems.Thm_ActuarialValuation_frDiscount_start
-- name    : ActuarialValuation.frDiscount_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:32.473428+00:00
-- url     : https://prove2.me/theorems/ad5fb587-27d8-4614-8ad4-056c1d365749
-- title:
--   Within-year survival and discount timing: frDiscount_start
-- statement:
--   The discount factor for an immediate cashflow at issue is one.
--
--   Mathematical relation:
--
--   $$
--   frDiscount\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount

namespace ActuarialValuation

theorem frDiscount_start (delta : ℝ) : frDiscount delta 0 = 1 := by sorry

end ActuarialValuation
