-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteedRisk_below
-- name    : ActuarialValuation.ulGuaranteedRisk_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:00.751557+00:00
-- url     : https://prove2.me/theorems/d23cab02-00d6-468f-8a61-7be45d9f2d5d
-- title:
--   Type A and B mortality strain and explicit guarantee: ulGuaranteedRisk_below
-- statement:
--   When the account is below the guarantee, the insured strain is precisely the difference.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteedRisk\_below
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk

namespace ActuarialValuation

theorem ulGuaranteedRisk_below (account floor : ℝ) (h : account≤floor) : ulGuaranteedNetRisk account floor = floor-account := by sorry

end ActuarialValuation
