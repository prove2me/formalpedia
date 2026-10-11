-- Prove2me | Theorems.Thm_ActuarialValuation_ulGuaranteePV_decomposition
-- name    : ActuarialValuation.ulGuaranteePV_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:53.073986+00:00
-- url     : https://prove2.me/theorems/34d236e2-fe3d-4364-af8e-b076d4e84ed5
-- title:
--   Path-dependent account evolution and stochastic guarantee pricing: ulGuaranteePV_decomposition
-- statement:
--   Under the actual finite scenario distribution, total guaranteed benefits equal account exposure plus distinct stochastic option-like insurer liability.
--
--   Mathematical relation:
--
--   $$
--   ulGuaranteePV\_decomposition
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 13 and 20, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.wiley-vch.de/en?isbn=9780471392903&option=com_eshop&title=Investment+Guarantees&view=product. The proposed model is rooted in Promislow chapter 13 and 20. The target Lean identity is an original derivation, not a verbatim published result. Published source page 201 concerns universal-life account valuation; this item is an original formal derived statement.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedPV
import Definitions.Def_actuarial_ulAccountPV
import Definitions.Def_actuarial_ulShortfallPV

namespace ActuarialValuation

theorem ulGuaranteePV_decomposition {m : ℕ} (prob discount account floor : Fin m→ℝ) : ulGuaranteedPV prob discount account floor = ulAccountPV prob discount account + ulShortfallPV prob discount account floor := by sorry

end ActuarialValuation
