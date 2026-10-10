-- Prove2me | Theorems.Thm_ActuarialValuation_frDueValue_nonneg
-- name    : ActuarialValuation.frDueValue_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:22:55.886993+00:00
-- url     : https://prove2.me/theorems/a4bb8ef6-455f-4bd4-8e62-7646490987b2
-- title:
--   Frequency-dependent annuity cashflow valuation: frDueValue_nonneg
-- statement:
--   Nonnegative due payments discounted by nonnegative factors and valid one-year mortality rates have nonnegative actuarial value.
--
--   Mathematical relation:
--
--   $$
--   frDueValue\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue

namespace ActuarialValuation

theorem frDueValue_nonneg (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) (hd : ∀ z, 0 ≤ discount z) (hp : ∀ k ∈ Finset.range n, 0 ≤ p k) (hq0 : ∀ k ∈ Finset.range n, 0 ≤ q k) (hq1 : ∀ k ∈ Finset.range n, q k ≤ 1) : 0 ≤ frDueValue c discount p q n m := by sorry

end ActuarialValuation
