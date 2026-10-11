-- Prove2me | Theorems.Thm_ActuarialValuation_ulAccountPath_recursion
-- name    : ActuarialValuation.ulAccountPath_recursion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:56.3961+00:00
-- url     : https://prove2.me/theorems/a59d6468-756c-4ce1-b9fe-f2637253335c
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPath_recursion
-- statement:
--   Successor account value reflects precisely the scheduled monthly premium, expenses, credited interest and insurance charge at period n.
--
--   Mathematical relation:
--
--   $$
--   ulAccountPath\_recursion
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath
import Definitions.Def_actuarial_ulTypeBNext

namespace ActuarialValuation

theorem ulAccountPath_recursion (initial : ℝ) (prem expenseRate flat interest mortality face : ℕ→ℝ) (n : ℕ) : ulAccountPath initial prem expenseRate flat interest mortality face (n+1) = ulTypeBNext (ulAccountPath initial prem expenseRate flat interest mortality face n) (prem n) (expenseRate n) (flat n) (interest n) (mortality n) (face n) := by sorry

end ActuarialValuation
