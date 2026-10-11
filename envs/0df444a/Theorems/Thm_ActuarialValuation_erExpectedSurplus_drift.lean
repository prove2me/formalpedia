-- Prove2me | Theorems.Thm_ActuarialValuation_erExpectedSurplus_drift
-- name    : ActuarialValuation.erExpectedSurplus_drift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:52:50.077833+00:00
-- url     : https://prove2.me/theorems/14bbf1c7-4382-4a08-8ee1-f332ba5b80f5
-- title:
--   Expected aggregate claims and positive safety loading: erExpectedSurplus_drift
-- statement:
--   Net profit drift over a subsequent period equals premium less expected aggregate claim rate. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Net profit drift over a subsequent period equals premium less} \\ \text{expected aggregate claim rate.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

namespace ActuarialValuation

theorem erExpectedSurplus_drift (u c lambda beta s t : ℝ) : erExpectedSurplus u c lambda beta (s+t)-erExpectedSurplus u c lambda beta s=t*(c-lambda/beta) := by sorry

end ActuarialValuation
