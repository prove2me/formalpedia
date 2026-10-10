-- Prove2me | Theorems.Thm_ActuarialValuation_frReserve_zero_mortality
-- name    : ActuarialValuation.frReserve_zero_mortality
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:44.044112+00:00
-- url     : https://prove2.me/theorems/09de3156-4bea-45ad-8d54-e9d1ab90a38e
-- title:
--   Fractional premiums and policy reserves: frReserve_zero_mortality
-- statement:
--   When annual mortality is zero, conditional reserve reduces to accumulated opening assets and premium.
--
--   Mathematical relation:
--
--   $$
--   frReserve\_zero\_mortality
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frFractionalReserve

namespace ActuarialValuation

theorem frReserve_zero_mortality (assets premium benefit s growth endDiscount : ℝ) : frFractionalReserve assets premium benefit 0 s growth endDiscount = (assets+premium)*growth := by sorry

end ActuarialValuation
