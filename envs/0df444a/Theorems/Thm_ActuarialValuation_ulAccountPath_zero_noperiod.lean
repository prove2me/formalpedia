-- Prove2me | Theorems.Thm_ActuarialValuation_ulAccountPath_zero_noperiod
-- name    : ActuarialValuation.ulAccountPath_zero_noperiod
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:15.158813+00:00
-- url     : https://prove2.me/theorems/2052a902-8900-4c5b-932f-cb055b22ea09
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPath_zero_noperiod
-- statement:
--   Without any premiums, charges or growth, an account remains at its initial balance over any number of policy periods.
--
--   Mathematical relation:
--
--   $$
--   ulAccountPath\_zero\_noperiod
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPath

namespace ActuarialValuation

theorem ulAccountPath_zero_noperiod (initial : ℝ) (n : ℕ) : ulAccountPath initial (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) n = initial := by sorry

end ActuarialValuation
