-- Prove2me | Theorems.Thm_ActuarialValuation_ulAllocated_full
-- name    : ActuarialValuation.ulAllocated_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:14.116272+00:00
-- url     : https://prove2.me/theorems/503eefd0-ab04-47a8-b02f-c8bb5ba0859c
-- title:
--   Monthly account premium expenses and insurance charges: ulAllocated_full
-- statement:
--   With zero proportional expense, the full premium reaches the account.
--
--   Mathematical relation:
--
--   $$
--   ulAllocated\_full
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

theorem ulAllocated_full (prem : ℝ) : ulAllocatedPremium prem 0 = prem := by sorry

end ActuarialValuation
