-- Prove2me | Theorems.Thm_ActuarialValuation_erRuinCandidate_derivative
-- name    : ActuarialValuation.erRuinCandidate_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:01:30.567838+00:00
-- url     : https://prove2.me/theorems/3ad9fc4e-8dc2-4a48-8f3d-48065e12175a
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRuinCandidate_derivative
-- statement:
--   The candidate's capital derivative is genuinely computed by exponential differentiation. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The candidate's capital derivative is genuinely computed by} \\ \text{exponential differentiation.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erRuinCandidate
import Definitions.Def_actuarial_erRuinDerivativeRHS

namespace ActuarialValuation

theorem erRuinCandidate_derivative (lambda c beta u : ℝ) : HasDerivAt (erRuinCandidate lambda c beta) (erRuinDerivativeRHS lambda c beta u) u := by sorry

end ActuarialValuation
