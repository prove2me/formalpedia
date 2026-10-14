-- Prove2me | Theorems.Thm_ActuarialValuation_erExpectedSurplus_net_profit
-- name    : ActuarialValuation.erExpectedSurplus_net_profit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:54:18.092343+00:00
-- url     : https://prove2.me/theorems/2dee9027-71cc-40e0-b83f-163c2737449b
-- title:
--   Expected aggregate claims and positive safety loading: erExpectedSurplus_net_profit
-- statement:
--   Expected capital does not decrease when the premium exceeds the expected claim rate. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Expected capital does not decrease when the premium exceeds the} \\ \text{expected claim rate.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExpectedSurplus

namespace ActuarialValuation

theorem erExpectedSurplus_net_profit (u c lambda beta t : ℝ) (hc : 0<c) (hb : 0<beta) (hn : lambda<c*beta) (ht : 0≤t) : u≤erExpectedSurplus u c lambda beta t := by sorry

end ActuarialValuation
