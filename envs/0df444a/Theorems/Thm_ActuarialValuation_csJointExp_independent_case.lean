-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_independent_case
-- name    : ActuarialValuation.csJointExp_independent_case
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:24.479122+00:00
-- url     : https://prove2.me/theorems/76ca8825-21c8-40ee-a030-0e799f2ea133
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_independent_case
-- statement:
--   When common-shock intensity is zero, survivor factorisation reduces to the independent primitive model.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_independent\_case
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointExp
import Definitions.Def_actuarial_csMarginalOneExp
import Definitions.Def_actuarial_csMarginalTwoExp

namespace ActuarialValuation

theorem csJointExp_independent_case (a b s t : ℝ) : csJointExp a b 0 s t = csMarginalOneExp a 0 s * csMarginalTwoExp b 0 t := by sorry

end ActuarialValuation
