-- Prove2me | Theorems.Thm_ActuarialValuation_nhTransition_alive_row
-- name    : ActuarialValuation.nhTransition_alive_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:07:08.401961+00:00
-- url     : https://prove2.me/theorems/af1b608d-9bd2-4ab0-8764-79ad69a5c7f6
-- title:
--   Three-state transition probabilities and Chapman–Kolmogorov: nhTransition_alive_row
-- statement:
--   All three probabilities in the active row add to one. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   P_{00}(s,t)=e^{-(H(t)-H(s))},\quad P_{01}(s,t)=p(1-P_{00}(s,t))
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 30. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Frederik Møller and colleagues, Multi-state modeling in the mathematics of life insurance, https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Nonstationary linear hazard, competing exits, absorbing three-state transition laws and differentiable integral prospective reserves. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition

namespace ActuarialValuation

theorem nhTransition_alive_row (a b p s t : ℝ) : (∑ j : Fin 3, nhTransition a b p s t 0 j)=1 := by sorry

end ActuarialValuation
