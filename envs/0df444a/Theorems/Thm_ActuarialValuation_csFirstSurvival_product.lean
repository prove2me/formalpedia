-- Prove2me | Theorems.Thm_ActuarialValuation_csFirstSurvival_product
-- name    : ActuarialValuation.csFirstSurvival_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:08.772629+00:00
-- url     : https://prove2.me/theorems/e3484d0c-f579-4c51-8fed-44529d8bbc00
-- title:
--   Independent-shock Marshall–Olkin survivor law: csFirstSurvival_product
-- statement:
--   The first-failure survivor function is the product of primitive constant-hazard survivor factors.
--
--   Mathematical relation:
--
--   $$
--   csFirstSurvival\_product
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

theorem csFirstSurvival_product (a b c t : ℝ) : csFirstExp a b c t = Real.exp (-a*t) * Real.exp (-b*t) * Real.exp (-c*t) := by sorry

end ActuarialValuation
