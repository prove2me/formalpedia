-- Prove2me | Theorems.Thm_ActuarialValuation_ulAccountPV_zero
-- name    : ActuarialValuation.ulAccountPV_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:26.477605+00:00
-- url     : https://prove2.me/theorems/70b9f055-6bbc-4086-bc17-883b6ac2916a
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulAccountPV_zero
-- statement:
--   An everywhere-zero account produces no discounted value.
--
--   Mathematical relation:
--
--   $$
--   ulAccountPV\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAccountPV

namespace ActuarialValuation

theorem ulAccountPV_zero {m : ℕ} (prob discount : Fin m → ℝ) : ulAccountPV prob discount (fun _ => 0) = 0 := by sorry

end ActuarialValuation
