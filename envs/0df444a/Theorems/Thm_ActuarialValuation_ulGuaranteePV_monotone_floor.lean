-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteePV_monotone_floor
-- name    : ActuarialValuation.ulGuaranteePV_monotone_floor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:42:06.394983+00:00
-- url     : https://prove2.me/theorems/49319e34-dc11-465d-a2ff-7b21b16dbe81
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePV_monotone_floor
-- statement:
--   Increasing every scenario's guaranteed floor cannot reduce the expected benefit liability under nonnegative state prices.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteePV\_monotone\_floor
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedPV

namespace ActuarialValuation

theorem ulGuaranteePV_monotone_floor {m : ℕ} (prob discount account floor1 floor2 : Fin m → ℝ) (hp : ∀ ω,0≤prob ω) (hd : ∀ ω,0≤discount ω) (hfloor : ∀ ω,floor1 ω≤floor2 ω) : ulGuaranteedPV prob discount account floor1 ≤ ulGuaranteedPV prob discount account floor2 := by sorry

end ActuarialValuation
