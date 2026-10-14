-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLoss_mono_loss
-- name    : ActuarialValuation.crStopLoss_mono_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:00.642245+00:00
-- url     : https://prove2.me/theorems/8821d90b-26c3-49d3-ae61-01b555eb66c6
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLoss_mono_loss
-- statement:
--   Monotone comparison of contract stop-loss costs under pointwise larger losses.
--
--   Mathematical relation:
--
--   $$
--   crStopLoss\_mono\_loss
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

theorem crStopLoss_mono_loss {n : ℕ} (p X Y : Fin n→ℝ) (d : ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crStopLoss p X d≤crStopLoss p Y d := by sorry

end ActuarialValuation
