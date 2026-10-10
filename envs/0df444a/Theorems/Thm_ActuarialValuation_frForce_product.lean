-- Prove2me | Theorems.Thm_ActuarialValuation_frForce_product
-- name    : ActuarialValuation.frForce_product
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:50.472368+00:00
-- url     : https://prove2.me/theorems/008a3602-443f-4bdf-bc73-38f6e691a910
-- title:
--   Within-year survival and discount timing: frForce_product
-- statement:
--   Exponential survival has the time-homogeneous multiplicative property for constant force mortality.
--
--   Mathematical relation:
--
--   $$
--   frForce\_product
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival

namespace ActuarialValuation

theorem frForce_product (mu s t : ℝ) : frForceSurvival mu (s+t) = frForceSurvival mu s * frForceSurvival mu t := by sorry

end ActuarialValuation
