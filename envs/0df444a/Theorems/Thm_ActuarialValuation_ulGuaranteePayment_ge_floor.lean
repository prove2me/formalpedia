-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteePayment_ge_floor
-- name    : ActuarialValuation.ulGuaranteePayment_ge_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:52.140563+00:00
-- url     : https://prove2.me/theorems/bd0bd5fd-0fe6-4f3b-ab1a-3752aa6a9d7f
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePayment_ge_floor
-- statement:
--   Guaranteed benefit pays at least the contractual floor at death or maturity.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteePayment\_ge\_floor
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

namespace ActuarialValuation

theorem ulGuaranteePayment_ge_floor (account floor : ℝ) : floor ≤ ulGuaranteePayment account floor := by sorry

end ActuarialValuation
