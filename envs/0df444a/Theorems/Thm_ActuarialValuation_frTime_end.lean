-- Prove2me | Theorems.Thm_ActuarialValuation_frTime_end
-- name    : ActuarialValuation.frTime_end
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:31.249267+00:00
-- url     : https://prove2.me/theorems/a96f7460-6c9a-45b3-bce0-6362a56b4da7
-- title:
--   Frequency-dependent annuity cashflow valuation: frTime_end
-- statement:
--   The end of the last immediate subperiod equals the next annual policy anniversary when frequency is positive.
--
--   Mathematical relation:
--
--   $$
--   frTime\_end
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frTime

namespace ActuarialValuation

theorem frTime_end (k m : ℕ) (hm : 0 < m) : frTime k m m = (k:ℝ)+1 := by sorry

end ActuarialValuation
