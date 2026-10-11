-- Prove2me | Theorems.Thm_ActuarialValuation_bnAmerican_exercise_when_optimal
-- name    : ActuarialValuation.bnAmerican_exercise_when_optimal
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:38.472846+00:00
-- url     : https://prove2.me/theorems/c26e99b2-7427-4ef6-9b88-a3bcab57d1db
-- title:
--   Two-period binomial recursion and American option exercise: bnAmerican_exercise_when_optimal
-- statement:
--   Exercise is optimal when the immediate payoff exceeds or equals the continuation value.
--
--   Mathematical relation:
--
--   $$
--   bnAmerican\_exercise\_when\_optimal
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

namespace ActuarialValuation

theorem bnAmerican_exercise_when_optimal (exercise continuation : ℝ) (h : continuation ≤ exercise) : bnAmericanNode exercise continuation = exercise := by sorry

end ActuarialValuation
