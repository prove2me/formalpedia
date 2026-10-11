-- Prove2me | Theorems.Thm_ActuarialValuation_erRuinCandidate_nonincreasing
-- name    : ActuarialValuation.erRuinCandidate_nonincreasing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T16:00:44.04079+00:00
-- url     : https://prove2.me/theorems/73d875b7-758e-4782-858b-eddc319f962f
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuinCandidate_nonincreasing
-- statement:
--   Larger starting capital cannot increase the explicit candidate ruin probability. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Larger starting capital cannot increase the explicit candidate} \\ \text{ruin probability.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRuinCandidate

namespace ActuarialValuation

theorem erRuinCandidate_nonincreasing (lambda c beta u v : ℝ) (hl : 0≤lambda) (hc : 0<c) (hb : 0<beta) (hn : lambda<c*beta) (h : u≤v) : erRuinCandidate lambda c beta v≤erRuinCandidate lambda c beta u := by sorry

end ActuarialValuation
