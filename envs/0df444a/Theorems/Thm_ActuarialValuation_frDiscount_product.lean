-- Prove2me | Theorems.Thm_ActuarialValuation_frDiscount_product
-- name    : ActuarialValuation.frDiscount_product
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:48.532459+00:00
-- url     : https://prove2.me/theorems/53ad4241-b1cb-432a-94d6-d92171e5d9cf
-- title:
--   Within-year survival and discount timing: frDiscount_product
-- statement:
--   Constant-interest discounting factors across adjacent durations.
--
--   Mathematical relation:
--
--   $$
--   frDiscount\_product
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount

namespace ActuarialValuation

theorem frDiscount_product (delta s t : ℝ) : frDiscount delta (s+t) = frDiscount delta s * frDiscount delta t := by sorry

end ActuarialValuation
