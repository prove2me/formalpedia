-- Prove2me | Theorems.Thm_ActuarialValuation_ctTwoState_death_row
-- name    : ActuarialValuation.ctTwoState_death_row
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:55:40.252278+00:00
-- url     : https://prove2.me/theorems/13be3d6a-d8d1-4e82-9a5f-063c9a8a3466
-- title:
--   Continuous two-status Markov survival and semigroup: ctTwoState_death_row
-- statement:
--   The absorbing death state cannot recover under the model. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{The absorbing death state cannot recover under the model.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctTwoState

namespace ActuarialValuation

theorem ctTwoState_death_row (mu t : ℝ) : ctTwoState mu t 1 0=0 ∧ ctTwoState mu t 1 1=1 := by sorry

end ActuarialValuation
