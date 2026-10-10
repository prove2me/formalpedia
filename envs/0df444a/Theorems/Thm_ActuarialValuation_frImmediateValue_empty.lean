-- Prove2me | Theorems.Thm_ActuarialValuation_frImmediateValue_empty
-- name    : ActuarialValuation.frImmediateValue_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:11.240033+00:00
-- url     : https://prove2.me/theorems/e6ce39ca-cc42-4835-99e2-259c4893a0ee
-- title:
--   Frequency-dependent annuity cashflow valuation: frImmediateValue_empty
-- statement:
--   A zero-year immediate annuity has no scheduled payment dates.
--
--   Mathematical relation:
--
--   $$
--   frImmediateValue\_empty
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue

namespace ActuarialValuation

theorem frImmediateValue_empty (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (m : ℕ) : frImmediateValue c discount p q 0 m = 0 := by sorry

end ActuarialValuation
