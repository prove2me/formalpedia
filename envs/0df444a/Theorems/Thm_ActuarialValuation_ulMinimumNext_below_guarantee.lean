-- Prove2me | Theorems.Thm_ActuarialValuation_ulMinimumNext_below_guarantee
-- name    : ActuarialValuation.ulMinimumNext_below_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:53.156058+00:00
-- url     : https://prove2.me/theorems/c18e3da4-7f33-4703-9db3-f44b7b193f8b
-- title:
--   Type A and B mortality strain and explicit guarantee: ulMinimumNext_below_guarantee
-- statement:
--   Under a valid mortality charge rate below one, the computed low-account case stays below the binding guaranteed benefit.
--
--   Mathematical relation:
--
--   $$
--   ulMinimumNext\_below\_guarantee
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext

namespace ActuarialValuation

theorem ulMinimumNext_below_guarantee (earned mortality floor : ℝ) (h : earned≤floor) (hm0 : 0≤mortality) (hm1 : mortality<1) : ulMinimumNext earned mortality floor ≤ floor := by sorry

end ActuarialValuation
