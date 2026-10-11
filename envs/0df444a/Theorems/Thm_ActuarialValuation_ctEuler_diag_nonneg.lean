-- Prove2me | Theorems.Thm_ActuarialValuation_ctEuler_diag_nonneg
-- name    : ActuarialValuation.ctEuler_diag_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T15:51:14.828741+00:00
-- url     : https://prove2.me/theorems/90bb75fd-386f-4b38-9e15-6c13c9d10a09
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctEuler_diag_nonneg
-- statement:
--   Step restriction ensures a nonnegative no-movement probability. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Step restriction ensures a nonnegative no-movement probability.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
import Definitions.Def_actuarial_ctEuler

namespace ActuarialValuation

theorem ctEuler_diag_nonneg (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i : Fin 3) (hs : h*ctRateOut r i ≤ 1) : 0 ≤ ctEuler r h i i := by sorry

end ActuarialValuation
