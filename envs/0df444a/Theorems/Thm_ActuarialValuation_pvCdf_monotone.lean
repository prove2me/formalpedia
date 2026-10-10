-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_monotone
-- name    : ActuarialValuation.pvCdf_monotone
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:54.505976+00:00
-- url     : https://prove2.me/theorems/0c008698-943b-407a-8886-457ce5643161
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_monotone
-- statement:
--   Loss CDF is monotone in its threshold, with exact treatment of atoms at the threshold.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_monotone
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_monotone {n : ℕ} (p loss : Fin n → ℝ) (x y : ℝ) (hp : ∀ i, 0 ≤ p i) (hxy : x ≤ y) : pvCdf p loss x ≤ pvCdf p loss y := by sorry

end ActuarialValuation
