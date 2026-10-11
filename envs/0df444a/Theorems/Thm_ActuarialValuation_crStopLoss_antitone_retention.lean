-- Prove2me | Theorems.Thm_ActuarialValuation_crStopLoss_antitone_retention
-- name    : ActuarialValuation.crStopLoss_antitone_retention
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:39:43.157451+00:00
-- url     : https://prove2.me/theorems/162aa9c6-b5e8-41d7-9f6d-d757e153e5bd
-- title:
--   Stop-loss risk comparison and limitations of floored risk principles: crStopLoss_antitone_retention
-- statement:
--   Increasing an insurance deductible reduces or preserves expected insurer excess-loss payments.
--
--   Mathematical relation:
--
--   $$
--   crStopLoss\_antitone\_retention
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss

namespace ActuarialValuation

theorem crStopLoss_antitone_retention {n : ℕ} (p X : Fin n→ℝ) (d e : ℝ) (hp : ∀ i,0≤p i) (hde : d≤e) : crStopLoss p X e≤crStopLoss p X d := by sorry

end ActuarialValuation
