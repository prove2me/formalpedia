-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteeShortfall_positive
-- name    : ActuarialValuation.ulGuaranteeShortfall_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:21.37859+00:00
-- url     : https://prove2.me/theorems/040f8e07-955c-4d02-ac9b-92d3446e53b2
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteeShortfall_positive
-- statement:
--   The guarantee top-up equals shortfall where the underlying account falls below the promised floor.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteeShortfall\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteeShortfall

namespace ActuarialValuation

theorem ulGuaranteeShortfall_positive (account floor : ℝ) (h : account<floor) : ulGuaranteeShortfall account floor = floor-account := by sorry

end ActuarialValuation
