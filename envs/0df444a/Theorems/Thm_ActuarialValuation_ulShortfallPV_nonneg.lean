-- Prove2me | Theorems.Thm_ActuarialValuation_ulShortfallPV_nonneg
-- name    : ActuarialValuation.ulShortfallPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:40.173985+00:00
-- url     : https://prove2.me/theorems/bda064f0-36fe-4229-b123-47b1ab2f8d5b
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulShortfallPV_nonneg
-- statement:
--   The expected discounted insurer guarantee cost is nonnegative when state probabilities and discount factors are nonnegative.
--
--   Mathematical relation:
--
--   $$
--   ulShortfallPV\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulShortfallPV

namespace ActuarialValuation

theorem ulShortfallPV_nonneg {m : ℕ} (prob discount account floor : Fin m → ℝ) (hp : ∀ ω, 0≤prob ω) (hd : ∀ ω, 0≤discount ω) : 0≤ulShortfallPV prob discount account floor := by sorry

end ActuarialValuation
