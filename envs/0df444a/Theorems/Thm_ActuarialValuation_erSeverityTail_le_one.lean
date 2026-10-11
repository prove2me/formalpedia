-- Prove2me | Theorems.Thm_ActuarialValuation_erSeverityTail_le_one
-- name    : ActuarialValuation.erSeverityTail_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:59:21.642808+00:00
-- url     : https://prove2.me/theorems/c50758d7-1308-42fc-af0e-f57208728000
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erSeverityTail_le_one
-- statement:
--   Proper exponential severity tail lies below one for a nonnegative level. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Proper exponential severity tail lies below one for a} \\ \text{nonnegative level.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail

namespace ActuarialValuation

theorem erSeverityTail_le_one (beta x : ℝ) (hb : 0≤beta) (hx : 0≤x) : erSeverityTail beta x≤1 := by sorry

end ActuarialValuation
