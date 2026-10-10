-- Prove2me | Theorems.Thm_ActuarialValuation_pvLoss_zero_premium
-- name    : ActuarialValuation.pvLoss_zero_premium
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:28.330979+00:00
-- url     : https://prove2.me/theorems/6f522210-fd5d-4487-9bf4-674c611cd61d
-- title:
--   Finite random present values of insurance benefits and premium streams: pvLoss_zero_premium
-- statement:
--   With no premium charge, realised prospective loss is the entire benefit present value.
--
--   Mathematical relation:
--
--   $$
--   pvLoss\_zero\_premium
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoss

namespace ActuarialValuation

theorem pvLoss_zero_premium {n : ℕ} (benefit annuity : Fin n → ℝ) (i : Fin n) : pvLoss benefit annuity 0 i = benefit i := by sorry

end ActuarialValuation
