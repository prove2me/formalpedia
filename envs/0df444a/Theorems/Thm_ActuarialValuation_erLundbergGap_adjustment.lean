-- Prove2me | Theorems.Thm_ActuarialValuation_erLundbergGap_adjustment
-- name    : ActuarialValuation.erLundbergGap_adjustment
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:57:06.133532+00:00
-- url     : https://prove2.me/theorems/fbb112ee-3b69-4dc1-bb86-29de649f87b9
-- title:
--   Lundberg adjustment coefficient and exponential-moment martingale factor: erLundbergGap_adjustment
-- statement:
--   The strictly positive adjustment root solves the actual Lundberg exponential moment condition. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The strictly positive adjustment root solves the actual} \\ \text{Lundberg exponential moment condition.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erLundbergGap

namespace ActuarialValuation

theorem erLundbergGap_adjustment (lambda premium beta : ℝ) (hl : 0<lambda) (hc : 0<premium) : erLundbergGap lambda premium beta (erAdjustment lambda premium beta)=0 := by sorry

end ActuarialValuation
