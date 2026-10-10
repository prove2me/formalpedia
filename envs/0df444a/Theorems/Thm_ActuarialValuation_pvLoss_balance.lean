-- Prove2me | Theorems.Thm_ActuarialValuation_pvLoss_balance
-- name    : ActuarialValuation.pvLoss_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:16.602978+00:00
-- url     : https://prove2.me/theorems/17a6ae1f-9c2b-44f6-a669-5a4d8bd79356
-- title:
--   Finite random present values of insurance benefits and premium streams: pvLoss_balance
-- statement:
--   In every insured state, prospective loss and received-premium PV exactly reconstruct the benefit PV.
--
--   Mathematical relation:
--
--   $$
--   pvLoss\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvLoss
import Definitions.Def_actuarial_pvPremium

namespace ActuarialValuation

theorem pvLoss_balance {n : ℕ} (benefit annuity : Fin n → ℝ) (premium : ℝ) (i : Fin n) : pvLoss benefit annuity premium i + pvPremium annuity premium i = benefit i := by sorry

end ActuarialValuation
