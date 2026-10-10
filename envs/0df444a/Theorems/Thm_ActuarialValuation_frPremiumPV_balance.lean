-- Prove2me | Theorems.Thm_ActuarialValuation_frPremiumPV_balance
-- name    : ActuarialValuation.frPremiumPV_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:06.652544+00:00
-- url     : https://prove2.me/theorems/368dccf5-c3a3-489f-94cc-6e281d85922c
-- title:
--   Fractional premiums and policy reserves: frPremiumPV_balance
-- statement:
--   Discounted fractional premium payments at the net rate exactly fund the benefit present value.
--
--   Mathematical relation:
--
--   $$
--   frPremiumPV\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frPremiumPV
import Definitions.Def_actuarial_frNetPremium

namespace ActuarialValuation

theorem frPremiumPV_balance (benefitPV annuityPV : ℝ) (ha : annuityPV ≠ 0) : frPremiumPV (frNetPremium benefitPV annuityPV) annuityPV = benefitPV := by sorry

end ActuarialValuation
