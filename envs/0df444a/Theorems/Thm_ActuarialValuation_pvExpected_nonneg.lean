-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpected_nonneg
-- name    : ActuarialValuation.pvExpected_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:29.720375+00:00
-- url     : https://prove2.me/theorems/f2da6b5e-331f-4689-9009-f02b4aa1a26b
-- title:
--   Equivalence premiums and loss variance: pvExpected_nonneg
-- statement:
--   A random loss that is everywhere nonnegative has a nonnegative expected present value.
--
--   Mathematical relation:
--
--   $$
--   pvExpected\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpected_nonneg {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hl : ∀ i, 0 ≤ loss i) : 0 ≤ pvExpected p loss := by sorry

end ActuarialValuation
