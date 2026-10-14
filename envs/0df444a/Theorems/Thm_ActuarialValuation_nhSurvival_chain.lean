-- Prove2me | Theorems.Thm_ActuarialValuation_nhSurvival_chain
-- name    : ActuarialValuation.nhSurvival_chain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:02:50.828321+00:00
-- url     : https://prove2.me/theorems/c83dc9ed-b315-49b3-b68b-70f9120d80a1
-- title:
--   Nonstationary intensity, exact absorption and generator conservation: nhSurvival_chain
-- statement:
--   Conditional survival composes over adjacent valuation dates. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \lambda(t)=a+bt,\quad H(t)=at+\frac{bt^2}{2}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 30. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Frederik Møller and colleagues, Multi-state modeling in the mathematics of life insurance, https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Nonstationary linear hazard, competing exits, absorbing three-state transition laws and differentiable integral prospective reserves. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival

namespace ActuarialValuation

theorem nhSurvival_chain (a b s u t : ℝ) : nhSurvival a b s t=nhSurvival a b s u*nhSurvival a b u t := by sorry

end ActuarialValuation
