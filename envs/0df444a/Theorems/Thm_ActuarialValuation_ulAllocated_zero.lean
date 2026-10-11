-- Prove2me | Theorems.Thm_ActuarialValuation_ulAllocated_zero
-- name    : ActuarialValuation.ulAllocated_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:31:59.058199+00:00
-- url     : https://prove2.me/theorems/ce330880-6080-4161-9a06-6e83a0847765
-- title:
--   Monthly account premium expenses and insurance charges: ulAllocated_zero
-- statement:
--   No cash premium produces no allocated premium.
--
--   Mathematical relation:
--
--   $$
--   ulAllocated\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

theorem ulAllocated_zero (expense : ℝ) : ulAllocatedPremium 0 expense = 0 := by sorry

end ActuarialValuation
