-- Prove2me | Theorems.Thm_ActuarialValuation_csFirstExp_nonincreasing
-- name    : ActuarialValuation.csFirstExp_nonincreasing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:09.643347+00:00
-- url     : https://prove2.me/theorems/19c4ee8d-9183-41a4-b16f-405cc23fd8ca
-- title:
--   Independent-shock Marshall–Olkin survivor law: csFirstExp_nonincreasing
-- statement:
--   First-failure survival is nonincreasing in the deadline under nonnegative hazard rates.
--
--   Mathematical relation:
--
--   $$
--   csFirstExp\_nonincreasing
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csFirstExp

namespace ActuarialValuation

theorem csFirstExp_nonincreasing (a b c s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hst : s ≤ t) : csFirstExp a b c t ≤ csFirstExp a b c s := by sorry

end ActuarialValuation
