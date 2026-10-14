-- Prove2me | Theorems.Thm_ActuarialValuation_erExpectedPremium_zero
-- name    : ActuarialValuation.erExpectedPremium_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:51:22.431905+00:00
-- url     : https://prove2.me/theorems/d9611352-2e64-4ccc-b2f3-e1b13955263e
-- title:
--   Expected aggregate claims and positive safety loading: erExpectedPremium_zero
-- statement:
--   Zero exposure produces zero gross premiums. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Zero exposure produces zero gross premiums.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedPremium

namespace ActuarialValuation

theorem erExpectedPremium_zero (premium : ℝ) : erExpectedPremium premium 0=0 := by sorry

end ActuarialValuation
