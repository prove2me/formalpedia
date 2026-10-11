-- Prove2me | Theorems.Thm_ActuarialValuation_ulAccountPath_issue
-- name    : ActuarialValuation.ulAccountPath_issue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:39.603036+00:00
-- url     : https://prove2.me/theorems/b119ada2-985a-42c6-85b5-49f3399c671e
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPath_issue
-- statement:
--   Account path begins with the actual issued initial funds, before the first premium receipt.
--
--   Mathematical relation:
--
--   $$
--   ulAccountPath\_issue
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath

namespace ActuarialValuation

theorem ulAccountPath_issue (initial : ℝ) (prem expenseRate flat interest mortality face : ℕ→ℝ) : ulAccountPath initial prem expenseRate flat interest mortality face 0 = initial := by sorry

end ActuarialValuation
