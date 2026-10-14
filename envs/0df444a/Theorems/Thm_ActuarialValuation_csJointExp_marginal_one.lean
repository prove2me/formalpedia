-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_marginal_one
-- name    : ActuarialValuation.csJointExp_marginal_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:11.95998+00:00
-- url     : https://prove2.me/theorems/eb9397c3-d8d0-46e9-a5e5-ae9535556716
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_marginal_one
-- statement:
--   At second threshold zero, positive-duration joint survivor reduces to the first marginal exponential law.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_marginal\_one
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

namespace ActuarialValuation

theorem csJointExp_marginal_one (a b c s : ℝ) (hs : 0 ≤ s) : csJointExp a b c s 0 = csMarginalOneExp a c s := by sorry

end ActuarialValuation
