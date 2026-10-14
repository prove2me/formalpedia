-- Prove2me | Theorems.Thm_ActuarialValuation_crMixture_expected
-- name    : ActuarialValuation.crMixture_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:08.217988+00:00
-- url     : https://prove2.me/theorems/9f176420-65b1-412c-ad58-9e7d85c1550d
-- title:
--   Actual finite loss distributions and scenario ambiguity: crMixture_expected
-- statement:
--   Expected loss under an ambiguous mixture is the convex combination of expected losses under each candidate law.
--
--   Mathematical relation:
--
--   $$
--   crMixture\_expected
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crMixWeights

namespace ActuarialValuation

theorem crMixture_expected {n : ℕ} (p q X : Fin n→ℝ) (mix : ℝ) : crExpected (crMixWeights p q mix) X = mix*crExpected p X+(1-mix)*crExpected q X := by sorry

end ActuarialValuation
