-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_le_one
-- name    : ActuarialValuation.pvCdf_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:26.98013+00:00
-- url     : https://prove2.me/theorems/bd73551e-0407-46e3-9d3a-9e7771d80079
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_le_one
-- statement:
--   The genuine finite loss CDF cannot exceed one when all masses are nonnegative and normalised.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_le\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_le_one {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i : Fin n, p i) = 1) : pvCdf p loss z ≤ 1 := by sorry

end ActuarialValuation
