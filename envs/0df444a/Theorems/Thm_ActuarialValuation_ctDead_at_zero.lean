-- Prove2me | Theorems.Thm_ActuarialValuation_ctDead_at_zero
-- name    : ActuarialValuation.ctDead_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T15:54:16.358572+00:00
-- url     : https://prove2.me/theorems/3d7cadd5-2aa6-403f-8495-659b91eea8cb
-- title:
--   Continuous two-status Markov survival and semigroup: ctDead_at_zero
-- statement:
--   There is no death mass over a zero time interval. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{There is no death mass over a zero time interval.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctDead

namespace ActuarialValuation

theorem ctDead_at_zero (mu : ℝ) : ctDead mu 0 = 0 := by sorry

end ActuarialValuation
