-- Prove2me | Theorems.Thm_ActuarialValuation_frConditional_start
-- name    : ActuarialValuation.frConditional_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:13.210978+00:00
-- url     : https://prove2.me/theorems/2faceeab-0e9e-4d5e-bbeb-8e6abd1cecb9
-- title:
--   Within-year survival and discount timing: frConditional_start
-- statement:
--   A survivor alive at fractional duration s survives a further zero duration with conditional probability one.
--
--   Mathematical relation:
--
--   $$
--   frConditional\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frConditionalUdd
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

theorem frConditional_start (q s : ℝ) (hs : frUddSurvival q s ≠ 0) : frConditionalUdd q s 0 = 1 := by sorry

end ActuarialValuation
