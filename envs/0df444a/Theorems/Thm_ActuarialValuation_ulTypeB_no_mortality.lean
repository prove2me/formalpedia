-- Prove2me | Theorems.Thm_ActuarialValuation_ulTypeB_no_mortality
-- name    : ActuarialValuation.ulTypeB_no_mortality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:09.500214+00:00
-- url     : https://prove2.me/theorems/814d428e-51ca-407b-8ddb-afa9252d9b9e
-- title:
--   Type A and B mortality strain and explicit guarantee: ulTypeB_no_mortality
-- statement:
--   Without insurance risk, Type B account retains pre-insurance earned funds.
--
--   Mathematical relation:
--
--   $$
--   ulTypeB\_no\_mortality
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulEarned

namespace ActuarialValuation

theorem ulTypeB_no_mortality (account prem expense flat interest face : ℝ) : ulTypeBNext account prem expense flat interest 0 face = ulEarned account prem expense flat interest := by sorry

end ActuarialValuation
