-- Prove2me | Theorems.Thm_ActuarialValuation_pvVariance_const
-- name    : ActuarialValuation.pvVariance_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:55.4946+00:00
-- url     : https://prove2.me/theorems/3c684d36-a67c-464c-ba55-7e2222ed0203
-- title:
--   Equivalence premiums and loss variance: pvVariance_const
-- statement:
--   A constant loss has zero distributional variance under properly normalised scenario probabilities.
--
--   Mathematical relation:
--
--   $$
--   pvVariance\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvVariance

namespace ActuarialValuation

theorem pvVariance_const {n : ℕ} (p : Fin n → ℝ) (c : ℝ) (hp : (∑ i : Fin n, p i) = 1) : pvVariance p (fun _ => c) = 0 := by sorry

end ActuarialValuation
