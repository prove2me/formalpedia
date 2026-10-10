-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_above_support
-- name    : ActuarialValuation.pvCdf_above_support
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:34.203011+00:00
-- url     : https://prove2.me/theorems/8d19bf03-5555-4dd0-ba4e-e1c256f15454
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_above_support
-- statement:
--   The entire probability mass lies below any threshold at least as large as the maximum realised loss.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_above\_support
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_above_support {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hs : (∑ i : Fin n, p i) = 1) (hmax : ∀ i, loss i ≤ z) : pvCdf p loss z = 1 := by sorry

end ActuarialValuation
