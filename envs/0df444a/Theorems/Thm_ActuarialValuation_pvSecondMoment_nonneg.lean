-- Prove2me | Theorems.Thm_ActuarialValuation_pvSecondMoment_nonneg
-- name    : ActuarialValuation.pvSecondMoment_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:41.216752+00:00
-- url     : https://prove2.me/theorems/7d4ad81f-03a8-4fa3-af02-094eb799605c
-- title:
--   Equivalence premiums and loss variance: pvSecondMoment_nonneg
-- statement:
--   Squared realised losses weighted by nonnegative probability masses have nonnegative second moments.
--
--   Mathematical relation:
--
--   $$
--   pvSecondMoment\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvSecondMoment

namespace ActuarialValuation

theorem pvSecondMoment_nonneg {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvSecondMoment p loss := by sorry

end ActuarialValuation
