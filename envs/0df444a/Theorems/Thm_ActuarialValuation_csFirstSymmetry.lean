-- Prove2me | Theorems.Thm_ActuarialValuation_csFirstSymmetry
-- name    : ActuarialValuation.csFirstSymmetry
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:21.724131+00:00
-- url     : https://prove2.me/theorems/97ad8b1e-6d60-415e-bfdc-5a9e866599e3
-- title:
--   Actual joint-lifetime events and cause partition: csFirstSymmetry
-- statement:
--   Order of idiosyncratic primitive risks does not change first failure.
--
--   Mathematical relation:
--
--   $$
--   csFirstSymmetry
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace ActuarialValuation

theorem csFirstSymmetry (U V Z : ℝ) : min U (min V Z) = min V (min U Z) := by sorry

end ActuarialValuation
