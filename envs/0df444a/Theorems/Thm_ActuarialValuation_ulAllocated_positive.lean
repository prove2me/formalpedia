-- Prove2me | Theorems.Thm_ActuarialValuation_ulAllocated_positive
-- name    : ActuarialValuation.ulAllocated_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:27.885341+00:00
-- url     : https://prove2.me/theorems/94284152-897a-420c-a543-6ff0294f2a40
-- title:
--   Monthly account premium expenses and insurance charges: ulAllocated_positive
-- statement:
--   An expense rate in the unit interval cannot create a negative allocated premium from a nonnegative contribution.
--
--   Mathematical relation:
--
--   $$
--   ulAllocated\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAllocatedPremium

namespace ActuarialValuation

theorem ulAllocated_positive (prem expense : ℝ) (hp : 0≤prem) (he0 : 0≤expense) (he1 : expense≤1) : 0≤ulAllocatedPremium prem expense := by sorry

end ActuarialValuation
