-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteedRisk_nonneg
-- name    : ActuarialValuation.ulGuaranteedRisk_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:28.651192+00:00
-- url     : https://prove2.me/theorems/4b8fa6a0-81ed-49a8-a83d-1140fdccc65a
-- title:
--   Type A and B mortality strain and explicit guarantee: ulGuaranteedRisk_nonneg
-- statement:
--   Minimum-death-benefit insurer risk amount cannot be negative.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteedRisk\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk

namespace ActuarialValuation

theorem ulGuaranteedRisk_nonneg (account floor : ℝ) : 0≤ulGuaranteedNetRisk account floor := by sorry

end ActuarialValuation
