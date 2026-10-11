-- Prove2me | Theorems.Thm_ActuarialValuation_erTrafficIntensity_lt_one
-- name    : ActuarialValuation.erTrafficIntensity_lt_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:53:54.944988+00:00
-- url     : https://prove2.me/theorems/3c8a7464-64e0-4986-bd5c-32d9ad5848a3
-- title:
--   Expected aggregate claims and positive safety loading: erTrafficIntensity_lt_one
-- statement:
--   Safety loading implies a claim-to-premium ratio strictly below one. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Safety loading implies a claim-to-premium ratio strictly below} \\ \text{one.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity

namespace ActuarialValuation

theorem erTrafficIntensity_lt_one (lambda c beta : ℝ) (hc : 0<c) (hb : 0<beta) (hn : lambda<c*beta) : erTrafficIntensity lambda c beta<1 := by sorry

end ActuarialValuation
