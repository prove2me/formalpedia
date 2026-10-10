-- Prove2me | Theorems.Thm_ActuarialValuation_pvTerm_within_cover
-- name    : ActuarialValuation.pvTerm_within_cover
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:56.10516+00:00
-- url     : https://prove2.me/theorems/b5f74e71-37c8-4d4b-9ea8-6ddc0c9d57ab
-- title:
--   Finite random present values of insurance benefits and premium streams: pvTerm_within_cover
-- statement:
--   A death within the covered term earns the year-end discounted sum insured.
--
--   Mathematical relation:
--
--   $$
--   pvTerm\_within\_cover
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvTermBenefit

namespace ActuarialValuation

theorem pvTerm_within_cover (benefit discount : ℕ → ℝ) (term k : ℕ) (h : k < term) : pvTermBenefit benefit discount term k = benefit k * discount (k+1) := by sorry

end ActuarialValuation
