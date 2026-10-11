-- Prove2me | Theorems.Thm_ActuarialValuation_nhCumulative_increasing
-- name    : ActuarialValuation.nhCumulative_increasing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:02:12.608396+00:00
-- url     : https://prove2.me/theorems/fdd573bd-61c3-426c-86a4-345ce379984a
-- title:
--   Nonstationary intensity, exact absorption and generator conservation: nhCumulative_increasing
-- statement:
--   Nonnegative hazard accumulates nondecreasing exposure. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_nhCumulative

namespace ActuarialValuation

theorem nhCumulative_increasing (a b s t : ℝ) (ha : 0≤a) (hb : 0≤b) (hs : 0≤s) (hst : s≤t) : nhCumulative a b s≤nhCumulative a b t := by sorry

end ActuarialValuation
