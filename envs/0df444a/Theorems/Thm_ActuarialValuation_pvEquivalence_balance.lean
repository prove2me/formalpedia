-- Prove2me | Theorems.Thm_ActuarialValuation_pvEquivalence_balance
-- name    : ActuarialValuation.pvEquivalence_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:40.464489+00:00
-- url     : https://prove2.me/theorems/dc2cc4cb-8349-40ce-a6eb-a2413b8ffc30
-- title:
--   Equivalence premiums and loss variance: pvEquivalence_balance
-- statement:
--   An equivalence premium balances the expected insurance benefits and expected unit premium PV under nonzero denominator.
--
--   Mathematical relation:
--
--   $$
--   pvEquivalence\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvEquivalence_balance {n : ℕ} (p benefit annuity : Fin n → ℝ) (h : pvExpected p annuity ≠ 0) : pvEquivalencePremium p benefit annuity * pvExpected p annuity = pvExpected p benefit := by sorry

end ActuarialValuation
