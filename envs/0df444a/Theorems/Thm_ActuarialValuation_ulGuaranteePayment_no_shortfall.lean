-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteePayment_no_shortfall
-- name    : ActuarialValuation.ulGuaranteePayment_no_shortfall
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:03.892003+00:00
-- url     : https://prove2.me/theorems/93d7356b-00b0-424d-b5f8-0e213e0274cd
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePayment_no_shortfall
-- statement:
--   When the investment account exceeds the guarantee, insurer makes no option top-up.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteePayment\_no\_shortfall
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteePayment

namespace ActuarialValuation

theorem ulGuaranteePayment_no_shortfall (account floor : ℝ) (h : floor≤account) : ulGuaranteePayment account floor = account := by sorry

end ActuarialValuation
