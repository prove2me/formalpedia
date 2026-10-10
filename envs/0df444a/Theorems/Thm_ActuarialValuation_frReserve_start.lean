-- Prove2me | Theorems.Thm_ActuarialValuation_frReserve_start
-- name    : ActuarialValuation.frReserve_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:55.59761+00:00
-- url     : https://prove2.me/theorems/a2c73838-85eb-483e-8cc9-ba416f01c035
-- title:
--   Fractional premiums and policy reserves: frReserve_start
-- statement:
--   Immediately after a premium is received, before deaths and with unity accumulation, opening reserve equals assets plus premium.
--
--   Mathematical relation:
--
--   $$
--   frReserve\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve

namespace ActuarialValuation

theorem frReserve_start (assets premium benefit q : ℝ) (endDiscount : ℝ) : frFractionalReserve assets premium benefit q 0 1 endDiscount = assets+premium := by sorry

end ActuarialValuation
