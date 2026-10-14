-- Prove2me | Theorems.Thm_ActuarialValuation_ulAfterPremium_balance
-- name    : ActuarialValuation.ulAfterPremium_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:52.838979+00:00
-- url     : https://prove2.me/theorems/7d7aa609-d39e-4098-97f7-7af85bcf2214
-- title:
--   Monthly account premium expenses and insurance charges: ulAfterPremium_balance
-- statement:
--   Post-premium account plus fixed expense exactly reconstructs prior balance and allocated premium.
--
--   Mathematical relation:
--
--   $$
--   ulAfterPremium\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAfterPremium
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

theorem ulAfterPremium_balance (account prem expense flat : ℝ) : ulAfterPremium account prem expense flat + flat = account + ulAllocatedPremium prem expense := by sorry

end ActuarialValuation
