-- Prove2me | Theorems.Thm_ActuarialValuation_pvMass_nonneg
-- name    : ActuarialValuation.pvMass_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:58.812983+00:00
-- url     : https://prove2.me/theorems/2e1d0d0e-d80f-4589-8163-df59ea1aee32
-- title:
--   Actual loss distribution and percentile premium adequacy: pvMass_nonneg
-- statement:
--   Each exact-value mass of the finite loss distribution is nonnegative.
--
--   Mathematical relation:
--
--   $$
--   pvMass\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvMass

namespace ActuarialValuation

theorem pvMass_nonneg {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvMass p loss z := by sorry

end ActuarialValuation
