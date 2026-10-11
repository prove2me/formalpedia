-- Prove2me | Theorems.Thm_ActuarialValuation_ulAdjusted_rate_same
-- name    : ActuarialValuation.ulAdjusted_rate_same
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:35.02529+00:00
-- url     : https://prove2.me/theorems/7cd8845a-c95e-4d99-906d-5b07acbbcfa1
-- title:
--   Monthly account premium expenses and insurance charges: ulAdjusted_rate_same
-- statement:
--   If the insurance discount matches the account credited rate, the adjusted mortality charge equals the original mortality rate.
--
--   Mathematical relation:
--
--   $$
--   ulAdjusted\_rate\_same
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAdjustedMortality

namespace ActuarialValuation

theorem ulAdjusted_rate_same (interest mortality : ℝ) (hi : 1+interest ≠ 0) : ulAdjustedMortality interest interest mortality = mortality := by sorry

end ActuarialValuation
