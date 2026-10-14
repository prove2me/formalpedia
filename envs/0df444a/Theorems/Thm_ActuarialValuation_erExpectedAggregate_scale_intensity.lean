-- Prove2me | Theorems.Thm_ActuarialValuation_erExpectedAggregate_scale_intensity
-- name    : ActuarialValuation.erExpectedAggregate_scale_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:51:03.467985+00:00
-- url     : https://prove2.me/theorems/76cad005-1ee4-4abc-83d6-2a18549618a6
-- title:
--   Expected aggregate claims and positive safety loading: erExpectedAggregate_scale_intensity
-- statement:
--   Doubling the Poisson intensity doubles expected claim cost. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Doubling the Poisson intensity doubles expected claim cost.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedAggregate

namespace ActuarialValuation

theorem erExpectedAggregate_scale_intensity (lambda beta t k : ℝ) : erExpectedAggregate (k*lambda) beta t=k*erExpectedAggregate lambda beta t := by sorry

end ActuarialValuation
