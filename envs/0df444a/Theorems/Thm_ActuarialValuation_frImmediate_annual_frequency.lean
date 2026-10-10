-- Prove2me | Theorems.Thm_ActuarialValuation_frImmediate_annual_frequency
-- name    : ActuarialValuation.frImmediate_annual_frequency
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:48.101369+00:00
-- url     : https://prove2.me/theorems/19f68ff0-5089-4dd0-aa8c-084790caf890
-- title:
--   Frequency-dependent annuity cashflow valuation: frImmediate_annual_frequency
-- statement:
--   With one annual end-year payment and the annual life-table survival recursion, the two immediate valuation conventions reconcile.
--
--   Mathematical relation:
--
--   $$
--   frImmediate\_annual\_frequency
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frImmediateValue
import Definitions.Def_actuarial_frAnnualImmediateValue

namespace ActuarialValuation

theorem frImmediate_annual_frequency (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ) (hp : ∀ k ∈ Finset.range n, p (k+1) = p k * (1-q k)) : frImmediateValue c discount p q n 1 = frAnnualImmediateValue c discount p n := by sorry

end ActuarialValuation
