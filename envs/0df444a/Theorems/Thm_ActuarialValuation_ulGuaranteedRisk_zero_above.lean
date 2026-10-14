-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteedRisk_zero_above
-- name    : ActuarialValuation.ulGuaranteedRisk_zero_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:45.650111+00:00
-- url     : https://prove2.me/theorems/c1306d2f-8dcf-4691-b95d-54af5ffa4ef2
-- title:
--   Type A and B mortality strain and explicit guarantee: ulGuaranteedRisk_zero_above
-- statement:
--   No death guarantee risk remains when account exceeds the floor.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteedRisk\_zero\_above
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk

namespace ActuarialValuation

theorem ulGuaranteedRisk_zero_above (account floor : ℝ) (h : floor≤account) : ulGuaranteedNetRisk account floor = 0 := by sorry

end ActuarialValuation
