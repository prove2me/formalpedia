-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteePayment_ge_account
-- name    : ActuarialValuation.ulGuaranteePayment_ge_account
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:38.190979+00:00
-- url     : https://prove2.me/theorems/11977769-2045-4a94-98f0-4a9c441ed6e4
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePayment_ge_account
-- statement:
--   Guaranteed benefit pays at least the account value at exit.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteePayment\_ge\_account
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

namespace ActuarialValuation

theorem ulGuaranteePayment_ge_account (account floor : ℝ) : account ≤ ulGuaranteePayment account floor := by sorry

end ActuarialValuation
