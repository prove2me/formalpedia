-- Prove2me | Theorems.Thm_ActuarialValuation_ulEarned_nonneg
-- name    : ActuarialValuation.ulEarned_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:53.505352+00:00
-- url     : https://prove2.me/theorems/ae1e3e86-d576-46f7-9a5a-6368e2ac4ca8
-- title:
--   Monthly account premium expenses and insurance charges: ulEarned_nonneg
-- statement:
--   A nonnegative pre-interest account and nonnegative gross credited return preserve nonnegative pre-insurance balance.
--
--   Mathematical relation:
--
--   $$
--   ulEarned\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulAfterPremium

namespace ActuarialValuation

theorem ulEarned_nonneg (account prem expense flat interest : ℝ) (hbase : 0≤ulAfterPremium account prem expense flat) (hi : -1≤interest) : 0≤ulEarned account prem expense flat interest := by sorry

end ActuarialValuation
