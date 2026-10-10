-- Prove2me | Theorems.Thm_ActuarialValuation_frImmediateValue_zero_benefit
-- name    : ActuarialValuation.frImmediateValue_zero_benefit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:26.486976+00:00
-- url     : https://prove2.me/theorems/241f67a4-653d-4b18-a687-1ed9f83aa5fc
-- title:
--   Frequency-dependent annuity cashflow valuation: frImmediateValue_zero_benefit
-- statement:
--   A zero scheduled immediate annuity has exactly zero expected present value.
--
--   Mathematical relation:
--
--   $$
--   frImmediateValue\_zero\_benefit
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue

namespace ActuarialValuation

theorem frImmediateValue_zero_benefit (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : frImmediateValue (fun _ => 0) discount p q n m = 0 := by sorry

end ActuarialValuation
