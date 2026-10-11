-- Prove2me | Theorems.Thm_ActuarialValuation_crExpected_nonneg
-- name    : ActuarialValuation.crExpected_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:22.632347+00:00
-- url     : https://prove2.me/theorems/0c4273dc-e2dd-40e2-bc5a-ad3fa41ee421
-- title:
--   Actual finite loss distributions and scenario ambiguity: crExpected_nonneg
-- statement:
--   Nonnegative payments have nonnegative expected outgo.
--
--   Mathematical relation:
--
--   $$
--   crExpected\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

namespace ActuarialValuation

theorem crExpected_nonneg {n : ℕ} (p X : Fin n→ℝ) (hp : ∀ i,0≤p i) (hX : ∀ i,0≤X i) : 0≤crExpected p X := by sorry

end ActuarialValuation
