-- Prove2me | Theorems.Thm_ActuarialValuation_nhNonstationaryThiele_fundamental
-- name    : ActuarialValuation.nhNonstationaryThiele_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T18:23:54.175456+00:00
-- url     : https://prove2.me/theorems/c566fe0e-7636-4e83-9eee-b2c347d93aff
-- title:
--   Cause-contingent insurance and integral Thiele reserves: nhNonstationaryThiele_fundamental
-- statement:
--   A genuinely nonstationary three-state absorbing model conserves probability and its independently integral-defined prospective liability obeys the cause-contingent Thiele equation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_nhGenerator
import Definitions.Def_actuarial_nhTransition
import Definitions.Def_actuarial_nhReserve
import Definitions.Def_actuarial_nhThieleRHS

namespace ActuarialValuation

theorem nhNonstationaryThiele_fundamental (a b p δ B1 B2 M T t : ℝ) (ha : 0≤a) (hb : 0≤b) (hp : 0≤p) (hq : p≤1) (ht : 0≤t) (hT : t≤T) : ((∑ j : Fin 3, nhGenerator a b p t 0 j)=0) ∧ ((∑ j : Fin 3, nhTransition a b p t T 0 j)=1) ∧ (nhReserve a b p δ B1 B2 M T T=M) ∧ HasDerivAt (nhReserve a b p δ B1 B2 M T) (nhThieleRHS a b p δ B1 B2 t (nhReserve a b p δ B1 B2 M T t)) t := by sorry

end ActuarialValuation
