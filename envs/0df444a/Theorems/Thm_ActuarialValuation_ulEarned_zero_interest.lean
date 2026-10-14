-- Prove2me | Theorems.Thm_ActuarialValuation_ulEarned_zero_interest
-- name    : ActuarialValuation.ulEarned_zero_interest
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:11.51309+00:00
-- url     : https://prove2.me/theorems/06fe478c-80fc-4e5d-8c68-79f6eca04a40
-- title:
--   Monthly account premium expenses and insurance charges: ulEarned_zero_interest
-- statement:
--   With zero credited interest the pre-insurance closing account is the post-expense opening balance.
--
--   Mathematical relation:
--
--   $$
--   ulEarned\_zero\_interest
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAfterPremium

namespace ActuarialValuation

theorem ulEarned_zero_interest (account prem expense flat : ℝ) : ulEarned account prem expense flat 0 = ulAfterPremium account prem expense flat := by sorry

end ActuarialValuation
