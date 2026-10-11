-- Prove2me | Theorems.Thm_ActuarialValuation_ulMinimumNext_high
-- name    : ActuarialValuation.ulMinimumNext_high
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:11.812999+00:00
-- url     : https://prove2.me/theorems/6688d255-6f68-4d2e-a776-4dab0fac1bbd
-- title:
--   Type A and B mortality strain and explicit guarantee: ulMinimumNext_high
-- statement:
--   Where the pre-insurance account exceeds the guaranteed floor, there is no guarantee cost.
--
--   Mathematical relation:
--
--   $$
--   ulMinimumNext\_high
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext

namespace ActuarialValuation

theorem ulMinimumNext_high (earned mortality floor : ℝ) (h : floor<earned) : ulMinimumNext earned mortality floor = earned := by sorry

end ActuarialValuation
