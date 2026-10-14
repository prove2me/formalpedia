-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLoss_shift
-- name    : ActuarialValuation.crStopLoss_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:40:14.626174+00:00
-- url     : https://prove2.me/theorems/b3aa7019-d4bb-44b0-9209-2779a109f0b7
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLoss_shift
-- statement:
--   Adding the same certain cash amount to all losses and deductible leaves actual excess-loss distribution unchanged.
--
--   Mathematical relation:
--
--   $$
--   crStopLoss\_shift
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

theorem crStopLoss_shift {n : ℕ} (p X : Fin n→ℝ) (d c : ℝ) : crStopLoss p (fun i=>X i+c) (d+c) = crStopLoss p X d := by sorry

end ActuarialValuation
