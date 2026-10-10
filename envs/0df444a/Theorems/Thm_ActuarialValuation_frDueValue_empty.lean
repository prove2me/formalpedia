-- Prove2me | Theorems.Thm_ActuarialValuation_frDueValue_empty
-- name    : ActuarialValuation.frDueValue_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:20.218903+00:00
-- url     : https://prove2.me/theorems/517ac5c5-3c09-4297-98c1-38a5bc32a765
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue_empty
-- statement:
--   A zero-year due annuity has no payment times and zero present value.
--
--   Mathematical relation:
--
--   $$
--   frDueValue\_empty
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

namespace ActuarialValuation

theorem frDueValue_empty (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (m : ℕ) : frDueValue c discount p q 0 m = 0 := by sorry

end ActuarialValuation
