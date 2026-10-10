-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_nonneg
-- name    : ActuarialValuation.pvAdequacy_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:24.959768+00:00
-- url     : https://prove2.me/theorems/584f37bf-87f3-47a0-b05c-7fb978be64d1
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_nonneg
-- statement:
--   The exact probability of premium adequacy is nonnegative when event weights are valid.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

namespace ActuarialValuation

theorem pvAdequacy_nonneg {n : ℕ} (p benefit annuity : Fin n → ℝ) (premium : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvAdequacy p benefit annuity premium := by sorry

end ActuarialValuation
