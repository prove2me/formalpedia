-- Prove2me | Theorems.Thm_ActuarialValuation_erSeverityTail_positive
-- name    : ActuarialValuation.erSeverityTail_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:58:52.670609+00:00
-- url     : https://prove2.me/theorems/7d03cad2-aef9-4cfb-b088-1ea0fe300a30
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erSeverityTail_positive
-- statement:
--   The exponential survival tail is positive for every finite real threshold. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The exponential survival tail is positive for every finite real} \\ \text{threshold.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erSeverityTail

namespace ActuarialValuation

theorem erSeverityTail_positive (beta x : ℝ) : 0<erSeverityTail beta x := by sorry

end ActuarialValuation
