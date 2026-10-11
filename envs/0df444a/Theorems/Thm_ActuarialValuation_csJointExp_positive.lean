-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_positive
-- name    : ActuarialValuation.csJointExp_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:33.411297+00:00
-- url     : https://prove2.me/theorems/9b5ffceb-abce-409c-b464-b356978f526a
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_positive
-- statement:
--   Finite exponential primitive hazard parameters give strictly positive modeled joint survival.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_positive
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

namespace ActuarialValuation

theorem csJointExp_positive (a b c s t : ℝ) : 0 < csJointExp a b c s t := by sorry

end ActuarialValuation
