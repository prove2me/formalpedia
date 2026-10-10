-- Prove2me | Theorems.Thm_ActuarialValuation_pvAdequacy_above_threshold
-- name    : ActuarialValuation.pvAdequacy_above_threshold
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:29.041867+00:00
-- url     : https://prove2.me/theorems/dccc7e2a-db9d-4d47-99d5-7aab4157bc8d
-- title:
--   Actual loss distribution and percentile premium adequacy: pvAdequacy_above_threshold
-- statement:
--   A percentile premium adequacy condition on alpha is an actual tail-probability requirement for the prospective loss distribution.
--
--   Mathematical relation:
--
--   $$
--   pvAdequacy\_above\_threshold
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss

namespace ActuarialValuation

theorem pvAdequacy_above_threshold {n : ℕ} (p benefit annuity : Fin n → ℝ) (P α : ℝ) (hα : α ≤ pvAdequacy p benefit annuity P) : α ≤ pvCdf p (pvLoss benefit annuity P) 0 := by sorry

end ActuarialValuation
