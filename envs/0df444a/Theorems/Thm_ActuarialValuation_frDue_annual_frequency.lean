-- Prove2me | Theorems.Thm_ActuarialValuation_frDue_annual_frequency
-- name    : ActuarialValuation.frDue_annual_frequency
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:29.77902+00:00
-- url     : https://prove2.me/theorems/e3f6ad99-1843-41cf-a2d2-4e807c1a124d
-- title:
--   Frequency-dependent annuity cashflow valuation: frDue_annual_frequency
-- statement:
--   With a single payment per year, m-thly due valuation reduces exactly to annual due valuation.
--
--   Mathematical relation:
--
--   $$
--   frDue\_annual\_frequency
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
import Definitions.Def_actuarial_frAnnualDueValue

namespace ActuarialValuation

theorem frDue_annual_frequency (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ) : frDueValue c discount p q n 1 = frAnnualDueValue c discount p n := by sorry

end ActuarialValuation
