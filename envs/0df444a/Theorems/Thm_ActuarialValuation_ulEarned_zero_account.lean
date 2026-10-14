-- Prove2me | Theorems.Thm_ActuarialValuation_ulEarned_zero_account
-- name    : ActuarialValuation.ulEarned_zero_account
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:32.893002+00:00
-- url     : https://prove2.me/theorems/d2d2e2df-392c-48f6-b988-92f44f79c64b
-- title:
--   Monthly account premium expenses and insurance charges: ulEarned_zero_account
-- statement:
--   Newly issued account with no initial fund accumulates only the allocated premium less fixed expense.
--
--   Mathematical relation:
--
--   $$
--   ulEarned\_zero\_account
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

theorem ulEarned_zero_account (prem expense flat interest : ℝ) : ulEarned 0 prem expense flat interest = (ulAllocatedPremium prem expense-flat)*(1+interest) := by sorry

end ActuarialValuation
