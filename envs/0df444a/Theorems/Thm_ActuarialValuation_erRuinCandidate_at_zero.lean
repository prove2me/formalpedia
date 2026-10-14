-- Prove2me | Theorems.Thm_ActuarialValuation_erRuinCandidate_at_zero
-- name    : ActuarialValuation.erRuinCandidate_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:59:50.483684+00:00
-- url     : https://prove2.me/theorems/c6df163f-e96a-488c-b8dc-2c6433980708
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuinCandidate_at_zero
-- statement:
--   Ruin candidate at zero capital equals premium traffic intensity. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Ruin candidate at zero capital equals premium traffic} \\ \text{intensity.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity
import Definitions.Def_actuarial_erRuinCandidate

namespace ActuarialValuation

theorem erRuinCandidate_at_zero (lambda c beta : ℝ) : erRuinCandidate lambda c beta 0=erTrafficIntensity lambda c beta := by sorry

end ActuarialValuation
