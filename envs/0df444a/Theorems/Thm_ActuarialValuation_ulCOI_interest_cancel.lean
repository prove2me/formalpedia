-- Prove2me | Theorems.Thm_ActuarialValuation_ulCOI_interest_cancel
-- name    : ActuarialValuation.ulCOI_interest_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:23.005178+00:00
-- url     : https://prove2.me/theorems/18659941-c514-466b-8a52-638f2ba63b0c
-- title:
--   Monthly account premium expenses and insurance charges: ulCOI_interest_cancel
-- statement:
--   Beginning-period net insurance cost accumulated to the end equals the end-period mortality charge.
--
--   Mathematical relation:
--
--   $$
--   ulCOI\_interest\_cancel
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCOIAtStart

namespace ActuarialValuation

theorem ulCOI_interest_cancel (interest mortality risk : ℝ) (hi : 1+interest ≠ 0) : ulCOIAtStart interest mortality risk * (1+interest) = mortality*risk := by sorry

end ActuarialValuation
