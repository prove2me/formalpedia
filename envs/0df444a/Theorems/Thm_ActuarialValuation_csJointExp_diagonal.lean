-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_diagonal
-- name    : ActuarialValuation.csJointExp_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:51.870985+00:00
-- url     : https://prove2.me/theorems/93d0d737-f011-4705-bf7b-b82f68767b0a
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_diagonal
-- statement:
--   Joint survival to a common horizon is the survival of the first primitive failure time.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_diagonal
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
import Definitions.Def_actuarial_csFirstExp

namespace ActuarialValuation

theorem csJointExp_diagonal (a b c t : ℝ) : csJointExp a b c t t = csFirstExp a b c t := by sorry

end ActuarialValuation
