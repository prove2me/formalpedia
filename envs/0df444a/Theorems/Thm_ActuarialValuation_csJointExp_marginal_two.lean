-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_marginal_two
-- name    : ActuarialValuation.csJointExp_marginal_two
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:37:36.751674+00:00
-- url     : https://prove2.me/theorems/6e6ca773-eae3-4514-bd14-d9b9bd1b1654
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_marginal_two
-- statement:
--   At first threshold zero, joint survivor reduces to the second marginal law.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_marginal\_two
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
import Definitions.Def_actuarial_csMarginalTwoExp

namespace ActuarialValuation

theorem csJointExp_marginal_two (a b c t : ℝ) (ht : 0 ≤ t) : csJointExp a b c 0 t = csMarginalTwoExp b c t := by sorry

end ActuarialValuation
