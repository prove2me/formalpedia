-- Prove2me | Theorems.Thm_ActuarialValuation_ulMinimumNext_low_balance
-- name    : ActuarialValuation.ulMinimumNext_low_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:40.408925+00:00
-- url     : https://prove2.me/theorems/7511371a-bb47-4a3a-af55-a5915107f58d
-- title:
--   Type A and B mortality strain and explicit guarantee: ulMinimumNext_low_balance
-- statement:
--   The minimum-guarantee account solution satisfies the implicit end-of-period mortality strain balance in the guarantee-binding region.
--
--   Mathematical relation:
--
--   $$
--   ulMinimumNext\_low\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext

namespace ActuarialValuation

theorem ulMinimumNext_low_balance (earned mortality floor : ℝ) (h : earned≤floor) (hm : 1-mortality ≠ 0) : ulMinimumNext earned mortality floor * (1-mortality) + mortality*floor = earned := by sorry

end ActuarialValuation
