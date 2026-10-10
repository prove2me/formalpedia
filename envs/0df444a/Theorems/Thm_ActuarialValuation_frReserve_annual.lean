-- Prove2me | Theorems.Thm_ActuarialValuation_frReserve_annual
-- name    : ActuarialValuation.frReserve_annual
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:25:14.864807+00:00
-- url     : https://prove2.me/theorems/7befa5c1-946f-4885-ba0e-a347a220adac
-- title:
--   Fractional premiums and policy reserves: frReserve_annual
-- statement:
--   The UDD fractional reserve at exactly one year equals the end-year survivor reserve using the same benefit-payment convention.
--
--   Mathematical relation:
--
--   $$
--   frReserve\_annual
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frAnnualReserve

namespace ActuarialValuation

theorem frReserve_annual (assets premium benefit q growth : ℝ) : frFractionalReserve assets premium benefit q 1 growth 1 = frAnnualReserve assets premium benefit q growth := by sorry

end ActuarialValuation
