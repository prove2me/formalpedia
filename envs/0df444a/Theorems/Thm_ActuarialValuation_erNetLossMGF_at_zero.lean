-- Prove2me | Theorems.Thm_ActuarialValuation_erNetLossMGF_at_zero
-- name    : ActuarialValuation.erNetLossMGF_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:57:28.750993+00:00
-- url     : https://prove2.me/theorems/7198478d-ae74-4cc9-942b-f1bcf7a6338e
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erNetLossMGF_at_zero
-- statement:
--   Transform of the net-loss process at test parameter zero equals one. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Transform of the net-loss process at test parameter zero equals} \\ \text{one.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erNetLossMGF

namespace ActuarialValuation

theorem erNetLossMGF_at_zero (lambda premium beta t : ℝ) (hb : beta≠0) : erNetLossMGF lambda premium beta 0 t=1 := by sorry

end ActuarialValuation
