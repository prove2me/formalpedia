-- Prove2me | Theorems.Thm_ActuarialValuation_nhGenerator_alive_row
-- name    : ActuarialValuation.nhGenerator_alive_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:05:27.889274+00:00
-- url     : https://prove2.me/theorems/4ef3302c-9a72-49a6-93ac-48b71e02e0f1
-- title:
--   Nonstationary intensity, exact absorption and generator conservation: nhGenerator_alive_row
-- statement:
--   Time-dependent generator conservation follows from exit allocation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_nhGenerator

namespace ActuarialValuation

theorem nhGenerator_alive_row (a b p t : ℝ) : (∑ j : Fin 3, nhGenerator a b p t 0 j)=0 := by sorry

end ActuarialValuation
