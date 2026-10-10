-- Prove2me | Theorems.Thm_ActuarialValuation_frUdd_nonneg
-- name    : ActuarialValuation.frUdd_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:57.698124+00:00
-- url     : https://prove2.me/theorems/13ecc264-8036-47f2-b2b4-fa3f1fdbe871
-- title:
--   Within-year survival and discount timing: frUdd_nonneg
-- statement:
--   Within-year survival remains nonnegative when annual mortality and elapsed duration belong to the unit interval.
--
--   Mathematical relation:
--
--   $$
--   frUdd\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

theorem frUdd_nonneg (q s : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ frUddSurvival q s := by sorry

end ActuarialValuation
