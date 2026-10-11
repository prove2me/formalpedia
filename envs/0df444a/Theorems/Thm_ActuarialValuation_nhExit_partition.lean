-- Prove2me | Theorems.Thm_ActuarialValuation_nhExit_partition
-- name    : ActuarialValuation.nhExit_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:04:33.589588+00:00
-- url     : https://prove2.me/theorems/7905a5dc-61fc-4701-b41f-5e7c02eea6e7
-- title:
--   Nonstationary intensity, exact absorption and generator conservation: nhExit_partition
-- statement:
--   Survival and two competing decrements exhaust every outcome. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_nhExitOne
import Definitions.Def_actuarial_nhExitTwo

namespace ActuarialValuation

theorem nhExit_partition (a b p s t : ℝ) : nhSurvival a b s t+nhExitOne a b p s t+nhExitTwo a b p s t=1 := by sorry

end ActuarialValuation
