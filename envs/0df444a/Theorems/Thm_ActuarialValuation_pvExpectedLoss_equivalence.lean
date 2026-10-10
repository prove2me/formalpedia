-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpectedLoss_equivalence
-- name    : ActuarialValuation.pvExpectedLoss_equivalence
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:54.149801+00:00
-- url     : https://prove2.me/theorems/eb18600b-3017-4f5d-b28d-207caa326fc2
-- title:
--   Equivalence premiums and loss variance: pvExpectedLoss_equivalence
-- statement:
--   The equivalence principle makes expected prospective insurance loss equal zero, provided premium payments have nonzero expected annuity value.
--
--   Mathematical relation:
--
--   $$
--   pvExpectedLoss\_equivalence
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpectedLoss_equivalence {n : ℕ} (p benefit annuity : Fin n → ℝ) (h : pvExpected p annuity ≠ 0) : pvExpectedLoss p benefit annuity (pvEquivalencePremium p benefit annuity) = 0 := by sorry

end ActuarialValuation
