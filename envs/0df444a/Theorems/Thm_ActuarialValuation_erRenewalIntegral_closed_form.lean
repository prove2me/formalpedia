-- Prove2me | Theorems.Thm_ActuarialValuation_erRenewalIntegral_closed_form
-- name    : ActuarialValuation.erRenewalIntegral_closed_form
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:02:28.251521+00:00
-- url     : https://prove2.me/theorems/f52a0879-d7f6-4f06-891e-1f73540265c1
-- title:
--   Explicit ruin candidate and exact renewal valuation: erRenewalIntegral_closed_form
-- statement:
--   Actual exponential severity integral equals the derived closed-form convolution for a nondegenerate Lundberg root. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Actual exponential severity integral equals the derived} \\ \text{closed-form convolution for a nondegenerate Lundberg root.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 438. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 23, sections 23.3–23.7; Hanspeter Schmidli, Risk Theory (2017), Springer Actuarial, https://link.springer.com/book/10.1007/978-3-319-72005-0; Palmowski et al. 2020, https://doi.org/10.1007/s13385-020-00223-4. Parent topic: Compound Poisson surplus with exponentially distributed claims, net profit, adjustment root, exact candidate ruin function and renewal differential/integral equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erTrafficIntensity
import Definitions.Def_actuarial_erAdjustment
import Definitions.Def_actuarial_erRenewalIntegral

namespace ActuarialValuation

theorem erRenewalIntegral_closed_form (lambda c beta u : ℝ) (hl : 0<lambda) (hc : 0<c) (hb : 0<beta) : erRenewalIntegral lambda c beta u = erTrafficIntensity lambda c beta * beta/(beta-erAdjustment lambda c beta) * (Real.exp (-(erAdjustment lambda c beta)*u)-Real.exp (-beta*u)) := by sorry

end ActuarialValuation
