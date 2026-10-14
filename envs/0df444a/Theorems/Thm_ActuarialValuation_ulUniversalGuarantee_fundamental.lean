-- Prove2me | Theorems.Thm_ActuarialValuation_ulUniversalGuarantee_fundamental
-- name    : ActuarialValuation.ulUniversalGuarantee_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:42:23.719456+00:00
-- url     : https://prove2.me/theorems/7b69a45d-ee9a-4961-ae29-b7c7ebece011
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulUniversalGuarantee_fundamental
-- statement:
--   The capstone reconciles distinct Type A and Type B universal-life insurance account recursions with a genuine random scenario-by-scenario decomposition of policyholder account value and the insurer's embedded investment guarantee liability.
--
--   Mathematical relation:
--
--   $$
--   ulUniversalGuarantee\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulTypeANext
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulGuaranteedPV
import Definitions.Def_actuarial_ulAccountPV
import Definitions.Def_actuarial_ulShortfallPV

namespace ActuarialValuation

theorem ulUniversalGuarantee_fundamental (account prem expense flat interest mortality face : ℝ) (hm : 1-mortality ≠ 0) {m : ℕ} (prob discount balances floors : Fin m → ℝ) : (ulTypeBNext account prem expense flat interest mortality face + mortality*face = ulEarned account prem expense flat interest) ∧ (ulTypeANext account prem expense flat interest mortality face*(1-mortality)+mortality*face = ulEarned account prem expense flat interest) ∧ (ulGuaranteedPV prob discount balances floors = ulAccountPV prob discount balances + ulShortfallPV prob discount balances floors) := by sorry

end ActuarialValuation
