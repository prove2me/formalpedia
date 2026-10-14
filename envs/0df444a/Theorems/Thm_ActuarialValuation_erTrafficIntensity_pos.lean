-- Prove2me | Theorems.Thm_ActuarialValuation_erTrafficIntensity_pos
-- name    : ActuarialValuation.erTrafficIntensity_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:53:32.678072+00:00
-- url     : https://prove2.me/theorems/e4625a72-fe1f-49f3-81c0-4904dd3c0412
-- title:
--   Expected aggregate claims and positive safety loading: erTrafficIntensity_pos
-- statement:
--   The claim traffic intensity is positive for positive claim arrivals and premiums. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The claim traffic intensity is positive for positive claim} \\ \text{arrivals and premiums.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity

namespace ActuarialValuation

theorem erTrafficIntensity_pos (lambda c beta : ℝ) (hl : 0<lambda) (hc : 0<c) (hb : 0<beta) : 0<erTrafficIntensity lambda c beta := by sorry

end ActuarialValuation
