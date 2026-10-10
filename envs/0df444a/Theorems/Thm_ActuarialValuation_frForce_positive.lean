-- Prove2me | Theorems.Thm_ActuarialValuation_frForce_positive
-- name    : ActuarialValuation.frForce_positive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:00.501689+00:00
-- url     : https://prove2.me/theorems/57b6fd19-f430-490f-b970-645af33c461c
-- title:
--   Within-year survival and discount timing: frForce_positive
-- statement:
--   An exponential constant-force survival factor remains strictly positive at finite times.
--
--   Mathematical relation:
--
--   $$
--   frForce\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival

namespace ActuarialValuation

theorem frForce_positive (mu t : ℝ) : 0 < frForceSurvival mu t := by sorry

end ActuarialValuation
