-- Prove2me | Theorems.Thm_ActuarialValuation_erExpectedSurplus_issue
-- name    : ActuarialValuation.erExpectedSurplus_issue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:52:01.462977+00:00
-- url     : https://prove2.me/theorems/e0392e63-b58c-4353-9bd8-ad21e3bcadc9
-- title:
--   Expected aggregate claims and positive safety loading: erExpectedSurplus_issue
-- statement:
--   Expected starting surplus is precisely starting risk capital. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Expected starting surplus is precisely starting risk capital.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

namespace ActuarialValuation

theorem erExpectedSurplus_issue (initial premium lambda beta : ℝ) : erExpectedSurplus initial premium lambda beta 0=initial := by sorry

end ActuarialValuation
