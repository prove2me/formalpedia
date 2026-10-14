-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_strict_dependence
-- name    : ActuarialValuation.csJointExp_strict_dependence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:12.870128+00:00
-- url     : https://prove2.me/theorems/c07b39be-926e-447f-84df-aedbaf17aa46
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_strict_dependence
-- statement:
--   A positive common-shock intensity and positive horizon yield strictly higher joint survival than the product of observed marginal survivals.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_strict\_dependence
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
import Definitions.Def_actuarial_csJointIndependentExp

namespace ActuarialValuation

theorem csJointExp_strict_dependence (a b c t : ℝ) (hc : 0 < c) (ht : 0 < t) : csJointIndependentExp a b c t < csJointExp a b c t t := by sorry

end ActuarialValuation
