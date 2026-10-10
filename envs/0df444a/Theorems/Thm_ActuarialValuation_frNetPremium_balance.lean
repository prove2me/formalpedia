-- Prove2me | Theorems.Thm_ActuarialValuation_frNetPremium_balance
-- name    : ActuarialValuation.frNetPremium_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:38.953245+00:00
-- url     : https://prove2.me/theorems/f5528391-1ea7-48ac-bd3f-4a83f3a35a7e
-- title:
--   Fractional premiums and policy reserves: frNetPremium_balance
-- statement:
--   With nonzero premium annuity, the net premium balances expected discounted benefits and premium receipts.
--
--   Mathematical relation:
--
--   $$
--   frNetPremium\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frNetPremium

namespace ActuarialValuation

theorem frNetPremium_balance (benefitPV annuityPV : ℝ) (ha : annuityPV ≠ 0) : frNetPremium benefitPV annuityPV * annuityPV = benefitPV := by sorry

end ActuarialValuation
