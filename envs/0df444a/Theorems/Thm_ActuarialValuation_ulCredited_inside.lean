-- Prove2me | Theorems.Thm_ActuarialValuation_ulCredited_inside
-- name    : ActuarialValuation.ulCredited_inside
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:35:29.162982+00:00
-- url     : https://prove2.me/theorems/15684a00-5818-49d3-92b2-067739192156
-- title:
--   Monthly account premium expenses and insurance charges: ulCredited_inside
-- statement:
--   With underlying return inside contract corridor, no floor or cap adjustment applies.
--
--   Mathematical relation:
--
--   $$
--   ulCredited\_inside
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCreditedRate

namespace ActuarialValuation

theorem ulCredited_inside (market participation floor cap : ℝ) (h1 : floor≤participation*market) (h2 : participation*market≤cap) : ulCreditedRate market participation floor cap = participation*market := by sorry

end ActuarialValuation
