-- Prove2me | Theorems.Thm_ActuarialValuation_erExponentialMGF_positive
-- name    : ActuarialValuation.erExponentialMGF_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:56:26.127162+00:00
-- url     : https://prove2.me/theorems/d5c469fa-7df5-4b34-b42d-c63740bd4f9c
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erExponentialMGF_positive
-- statement:
--   Exponential severity moment generating function is positive inside its radius. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Exponential severity moment generating function is positive} \\ \text{inside its radius.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExponentialMGF

namespace ActuarialValuation

theorem erExponentialMGF_positive (beta r : ℝ) (hb : 0<beta) (hr : r<beta) : 0<erExponentialMGF beta r := by sorry

end ActuarialValuation
