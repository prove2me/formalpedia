-- Prove2me | Theorems.Thm_ActuarialValuation_bnAmerican_two_step_dominate_european
-- name    : ActuarialValuation.bnAmerican_two_step_dominate_european
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:39:06.712162+00:00
-- url     : https://prove2.me/theorems/4e6650f9-7f1f-4a11-aebd-6d4aea93e684
-- title:
--   Two-period binomial recursion and American option exercise: bnAmerican_two_step_dominate_european
-- statement:
--   Two-period American option with the same terminal payoff opportunities is worth at least as much as its European counterpart.
--
--   Mathematical relation:
--
--   $$
--   bnAmerican\_two\_step\_dominate\_european
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice
import Definitions.Def_actuarial_bnAmericanTwoPeriod

namespace ActuarialValuation

theorem bnAmerican_two_step_dominate_european (R q immediate up down uu ud du dd : ℝ) (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : bnTwoStepPrice R q uu ud du dd ≤ bnAmericanTwoPeriod R q immediate up down uu ud du dd := by sorry

end ActuarialValuation
