-- Prove2me | Theorems.Thm_ActuarialValuation_csJointExp_product_relation
-- name    : ActuarialValuation.csJointExp_product_relation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:39:37.314273+00:00
-- url     : https://prove2.me/theorems/5945731d-7132-4f35-8dea-16d64a2e3827
-- title:
--   Independent-shock Marshall–Olkin survivor law: csJointExp_product_relation
-- statement:
--   The observed marginal-survival product includes the common-shock hazard twice, whereas joint survival includes it once.
--
--   Mathematical relation:
--
--   $$
--   csJointExp\_product\_relation
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 11, 17 and 19, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1080/01621459.1967.10482885. The proposed model is rooted in Promislow chapter 11, 17 and 19. The target Lean identity is an original derivation, not a verbatim published result. Published source page 271 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointIndependentExp
import Definitions.Def_actuarial_csFirstExp

namespace ActuarialValuation

theorem csJointExp_product_relation (a b c t : ℝ) : csJointIndependentExp a b c t = csFirstExp a b c t * Real.exp (-c*t) := by sorry

end ActuarialValuation
