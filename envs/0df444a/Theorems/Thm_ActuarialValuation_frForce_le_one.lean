-- Prove2me | Theorems.Thm_ActuarialValuation_frForce_le_one
-- name    : ActuarialValuation.frForce_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:16.040067+00:00
-- url     : https://prove2.me/theorems/23582836-f13a-4c52-9c31-935616a391e5
-- title:
--   Within-year survival and discount timing: frForce_le_one
-- statement:
--   With nonnegative mortality force and nonnegative elapsed time, exponential survival does not exceed one.
--
--   Mathematical relation:
--
--   $$
--   frForce\_le\_one
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival

namespace ActuarialValuation

theorem frForce_le_one (mu t : ℝ) (hm : 0 ≤ mu) (ht : 0 ≤ t) : frForceSurvival mu t ≤ 1 := by sorry

end ActuarialValuation
