-- Prove2me | Theorems.Thm_ActuarialValuation_erExponentialMGF_at_zero
-- name    : ActuarialValuation.erExponentialMGF_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:55:35.925504+00:00
-- url     : https://prove2.me/theorems/7ba4f0b9-472d-453a-95a4-09547c4a8189
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erExponentialMGF_at_zero
-- statement:
--   The exponential severity MGF is normalised at zero. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{The exponential severity MGF is normalised at zero.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExponentialMGF

namespace ActuarialValuation

theorem erExponentialMGF_at_zero (beta : ℝ) (hb : beta≠0) : erExponentialMGF beta 0=1 := by sorry

end ActuarialValuation
