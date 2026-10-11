-- Prove2me | Theorems.Thm_ActuarialValuation_nhTransition_identity
-- name    : ActuarialValuation.nhTransition_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T18:06:29.674379+00:00
-- url     : https://prove2.me/theorems/d69bfbfe-ddd7-4765-b871-92e2ee57e285
-- title:
--   Three-state transition probabilities and Chapman–Kolmogorov: nhTransition_identity
-- statement:
--   Exact transition matrix reduces to identity at zero horizon. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem nhTransition_identity (a b p t : ℝ) (i j : Fin 3) : nhTransition a b p t t i j=(if i=j then 1 else 0) := by sorry

end ActuarialValuation
