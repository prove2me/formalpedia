-- Prove2me | Theorems.Thm_ActuarialValuation_frUdd_death
-- name    : ActuarialValuation.frUdd_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:29.380088+00:00
-- url     : https://prove2.me/theorems/f61bcdb2-51b3-48e0-b3ce-8ede1bb99c4f
-- title:
--   Within-year survival and discount timing: frUdd_death
-- statement:
--   Death probability from an anniversary is the elapsed proportion multiplied by annual q under UDD.
--
--   Mathematical relation:
--
--   $$
--   frUdd\_death
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

theorem frUdd_death (q s : ℝ) : 1 - frUddSurvival q s = s*q := by sorry

end ActuarialValuation
