-- Prove2me | Theorems.Thm_ActuarialValuation_frReserve_balance
-- name    : ActuarialValuation.frReserve_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:20.485176+00:00
-- url     : https://prove2.me/theorems/3b71336d-ec25-4bd7-b3c4-cec9e0ad1f5e
-- title:
--   Fractional premiums and policy reserves: frReserve_balance
-- statement:
--   The fractional reserve survivorship balance exactly reconciles premium accumulation and the end-year death-benefit financing term.
--
--   Mathematical relation:
--
--   $$
--   frReserve\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival

namespace ActuarialValuation

theorem frReserve_balance (assets premium benefit q s growth endDiscount : ℝ) (hs : frUddSurvival q s ≠ 0) : frFractionalReserve assets premium benefit q s growth endDiscount * frUddSurvival q s + s*q*benefit*endDiscount = (assets+premium)*growth := by sorry

end ActuarialValuation
