-- Prove2me | Theorems.Thm_ActuarialValuation_ulTypeA_balance
-- name    : ActuarialValuation.ulTypeA_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:36:45.870979+00:00
-- url     : https://prove2.me/theorems/32e396ea-07c2-4d18-9349-bdb838120805
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeA_balance
-- statement:
--   The implicit Type A survivor-account equation is exactly solved when survival one minus mortality is nonzero.
--
--   Mathematical relation:
--
--   $$
--   ulTypeA\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeANext
import Definitions.Def_actuarial_ulEarned

namespace ActuarialValuation

theorem ulTypeA_balance (account prem expense flat interest mortality face : ℝ) (hm : 1-mortality ≠ 0) : ulTypeANext account prem expense flat interest mortality face * (1-mortality) + mortality*face = ulEarned account prem expense flat interest := by sorry

end ActuarialValuation
