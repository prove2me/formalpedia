-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLoss_nonnegative
-- name    : ActuarialValuation.crStopLoss_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:33.428319+00:00
-- url     : https://prove2.me/theorems/ddd468bd-4287-4908-8d20-b5d57a37e0b7
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLoss_nonnegative
-- statement:
--   Expected stop-loss excess is nonnegative under a valid finite probability law.
--
--   Mathematical relation:
--
--   $$
--   crStopLoss\_nonnegative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

theorem crStopLoss_nonnegative {n : ℕ} (p X : Fin n→ℝ) (d : ℝ) (hp : ∀ i,0≤p i) : 0≤crStopLoss p X d := by sorry

end ActuarialValuation
