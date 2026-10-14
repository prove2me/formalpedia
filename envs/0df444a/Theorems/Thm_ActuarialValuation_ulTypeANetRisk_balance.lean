-- Prove2me | Theorems.Thm_ActuarialValuation_ulTypeANetRisk_balance
-- name    : ActuarialValuation.ulTypeANetRisk_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:17.238124+00:00
-- url     : https://prove2.me/theorems/7984dc5a-f401-486a-954c-856f5118e399
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeANetRisk_balance
-- statement:
--   Net amount at risk plus survivor account equals the fixed contractual death benefit.
--
--   Mathematical relation:
--
--   $$
--   ulTypeANetRisk\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeANetRisk

namespace ActuarialValuation

theorem ulTypeANetRisk_balance (account face : ℝ) : ulTypeANetRisk account face + account = face := by sorry

end ActuarialValuation
