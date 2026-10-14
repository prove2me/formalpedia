-- Prove2me | Theorems.Thm_ActuarialValuation_erAdjustment_lt_beta
-- name    : ActuarialValuation.erAdjustment_lt_beta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:55:02.348375+00:00
-- url     : https://prove2.me/theorems/dfead2c3-d4c3-40a3-96fd-b7cca0c9d5ed
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erAdjustment_lt_beta
-- statement:
--   The adjustment exponent remains within the exponential severity MGF domain. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The adjustment exponent remains within the exponential severity} \\ \text{MGF domain.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment

namespace ActuarialValuation

theorem erAdjustment_lt_beta (lambda c beta : ℝ) (hl : 0<lambda) (hc : 0<c) : erAdjustment lambda c beta<beta := by sorry

end ActuarialValuation
