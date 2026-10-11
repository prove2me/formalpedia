-- Prove2me | Theorems.Thm_ActuarialValuation_ulCOI_zero_mortality
-- name    : ActuarialValuation.ulCOI_zero_mortality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:08.624549+00:00
-- url     : https://prove2.me/theorems/d86d3f8a-1aac-48d7-91da-c8646e8d6999
-- title:
--   Monthly account premium expenses and insurance charges: ulCOI_zero_mortality
-- statement:
--   No mortality exposure gives zero cost of insurance.
--
--   Mathematical relation:
--
--   $$
--   ulCOI\_zero\_mortality
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCOIAtStart

namespace ActuarialValuation

theorem ulCOI_zero_mortality (interest risk : ℝ) : ulCOIAtStart interest 0 risk = 0 := by sorry

end ActuarialValuation
