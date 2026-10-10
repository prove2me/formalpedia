-- Prove2me | Theorems.Thm_ActuarialValuation_csObservedFirst
-- name    : ActuarialValuation.csObservedFirst
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:37.454657+00:00
-- url     : https://prove2.me/theorems/f620f6e5-a770-4270-b5fd-1f2f626e15da
-- title:
--   Actual joint-lifetime events and cause partition: csObservedFirst
-- statement:
--   Minimum of observed lifetimes equals minimum of the three primitive event times.
--
--   Mathematical relation:
--
--   $$
--   csObservedFirst
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstFailure
import Definitions.Def_actuarial_csFirstLife
import Definitions.Def_actuarial_csSecondLife

namespace ActuarialValuation

theorem csObservedFirst {Ω : Type*} (U V Z : Ω → ℝ) (ω : Ω) : csFirstFailure U V Z ω = min (csFirstLife U Z ω) (csSecondLife V Z ω) := by sorry

end ActuarialValuation
