-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpectedLoss_split
-- name    : ActuarialValuation.pvExpectedLoss_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:23.620989+00:00
-- url     : https://prove2.me/theorems/a98b188d-f08e-41eb-a6bc-7607f8283a1f
-- title:
--   Equivalence premiums and loss variance: pvExpectedLoss_split
-- statement:
--   Expected insurance loss decomposes into expected benefit PV less annual premium rate times expected unit premium annuity PV.
--
--   Mathematical relation:
--
--   $$
--   pvExpectedLoss\_split
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpectedLoss_split {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) : pvExpectedLoss p benefit annuity premium = pvExpected p benefit - premium * pvExpected p annuity := by sorry

end ActuarialValuation
