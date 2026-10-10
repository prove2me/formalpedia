-- Prove2me | Theorems.Thm_ActuarialValuation_frTime_start
-- name    : ActuarialValuation.frTime_start
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:13.991978+00:00
-- url     : https://prove2.me/theorems/691e1c35-6a4a-4ea9-b883-9367732575ff
-- title:
--   Frequency-dependent annuity cashflow valuation: frTime_start
-- statement:
--   The first due instalment of policy year k occurs at integer duration k.
--
--   Mathematical relation:
--
--   $$
--   frTime\_start
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frTime

namespace ActuarialValuation

theorem frTime_start (k m : ℕ) : frTime k 0 m = (k:ℝ) := by sorry

end ActuarialValuation
