-- Prove2me | Theorems.Thm_ActuarialValuation_frUdd_split
-- name    : ActuarialValuation.frUdd_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:42.453483+00:00
-- url     : https://prove2.me/theorems/8d91a483-1bbe-4766-a7f8-7d587c67b57e
-- title:
--   Within-year survival and discount timing: frUdd_split
-- statement:
--   Survival decrement over a subsequent interval is proportional to its additional duration.
--
--   Mathematical relation:
--
--   $$
--   frUdd\_split
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

theorem frUdd_split (q s t : ℝ) : frUddSurvival q (s+t) = frUddSurvival q s - t*q := by sorry

end ActuarialValuation
