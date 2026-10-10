-- Prove2me | Theorems.Thm_ActuarialValuation_frDueValue_zero_frequency
-- name    : ActuarialValuation.frDueValue_zero_frequency
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:52.161365+00:00
-- url     : https://prove2.me/theorems/9b7722f6-53c8-4d01-aae8-57622a402eed
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue_zero_frequency
-- statement:
--   An empty subperiod index set contributes no payments; zero frequency is a mathematical empty case, not a valid policy mode.
--
--   Mathematical relation:
--
--   $$
--   frDueValue\_zero\_frequency
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

namespace ActuarialValuation

theorem frDueValue_zero_frequency (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ) : frDueValue c discount p q n 0 = 0 := by sorry

end ActuarialValuation
