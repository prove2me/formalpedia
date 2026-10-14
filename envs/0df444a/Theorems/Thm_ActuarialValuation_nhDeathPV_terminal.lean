-- Prove2me | Theorems.Thm_ActuarialValuation_nhDeathPV_terminal
-- name    : ActuarialValuation.nhDeathPV_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:20:20.124976+00:00
-- url     : https://prove2.me/theorems/bff9b134-b2fb-4453-a758-2d3544da7f60
-- title:
--   Cause-contingent insurance and integral Thiele reserves: nhDeathPV_terminal
-- statement:
--   No death/exit payment is owed after contract maturity. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   V'(t)=(\delta+\lambda(t))V(t)-\lambda(t)\bigl(pB_1+(1-p)B_2\bigr)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 30. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Frederik Møller and colleagues, Multi-state modeling in the mathematics of life insurance, https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Nonstationary linear hazard, competing exits, absorbing three-state transition laws and differentiable integral prospective reserves. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhDeathPV

namespace ActuarialValuation

theorem nhDeathPV_terminal (a b p δ B1 B2 T : ℝ) : nhDeathPV a b p δ B1 B2 T T=0 := by sorry

end ActuarialValuation
