-- Prove2me | Theorems.Thm_ActuarialValuation_frAnnualReserve_balance
-- name    : ActuarialValuation.frAnnualReserve_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:25:29.560373+00:00
-- url     : https://prove2.me/theorems/1d7a0531-99f9-47d0-bc8c-330c97f8ba01
-- title:
--   Fractional premiums and policy reserves: frAnnualReserve_balance
-- statement:
--   Full-year survivor reserve plus claim cost reconstructs accumulated premium and assets, conditional on nonzero annual survival.
--
--   Mathematical relation:
--
--   $$
--   frAnnualReserve\_balance
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frAnnualReserve

namespace ActuarialValuation

theorem frAnnualReserve_balance (assets premium benefit q growth : ℝ) (hq : 1-q ≠ 0) : frAnnualReserve assets premium benefit q growth * (1-q) + q*benefit = (assets+premium)*growth := by sorry

end ActuarialValuation
