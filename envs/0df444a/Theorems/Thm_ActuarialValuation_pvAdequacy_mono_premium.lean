-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_mono_premium
-- name    : ActuarialValuation.pvAdequacy_mono_premium
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:38.425789+00:00
-- url     : https://prove2.me/theorems/3c9be582-924c-494d-9a4b-e1d10359a85b
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_mono_premium
-- statement:
--   Increasing premium rates cannot reduce the fraction of adequately funded states when scenario premium annuity values are nonnegative.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_mono\_premium
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

namespace ActuarialValuation

theorem pvAdequacy_mono_premium {n : ℕ} (p benefit annuity : Fin n → ℝ) (P Q : ℝ) (hP : P ≤ Q) (ha : ∀ i, 0 ≤ annuity i) (hp : ∀ i, 0 ≤ p i) : pvAdequacy p benefit annuity P ≤ pvAdequacy p benefit annuity Q := by sorry

end ActuarialValuation
