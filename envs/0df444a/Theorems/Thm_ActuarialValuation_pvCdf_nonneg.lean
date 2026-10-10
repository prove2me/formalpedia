-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_nonneg
-- name    : ActuarialValuation.pvCdf_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:42.081598+00:00
-- url     : https://prove2.me/theorems/bec29187-5a6d-49e7-97fe-674427837496
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_nonneg
-- statement:
--   The probability of the event loss at most z is nonnegative.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_nonneg {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvCdf p loss z := by sorry

end ActuarialValuation
