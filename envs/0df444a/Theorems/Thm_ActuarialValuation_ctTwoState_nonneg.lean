-- Prove2me | Theorems.Thm_ActuarialValuation_ctTwoState_nonneg
-- name    : ActuarialValuation.ctTwoState_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:56:23.389412+00:00
-- url     : https://prove2.me/theorems/b2314095-5b6b-4527-9052-ec8b6d1ede14
-- title:
--   Continuous two-status Markov survival and semigroup: ctTwoState_nonneg
-- statement:
--   The entire two-state transition matrix is entrywise nonnegative. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{The entire two-state transition matrix is entrywise} \\ \text{nonnegative.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState

namespace ActuarialValuation

theorem ctTwoState_nonneg (mu t : ℝ) (hmu : 0 ≤ mu) (ht : 0 ≤ t) (i j : Fin 2) : 0 ≤ ctTwoState mu t i j := by sorry

end ActuarialValuation
