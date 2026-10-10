-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateDeductiblePremium_nonneg
-- name    : ActuarialValuation.aggregateDeductiblePremium_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:09.081049+00:00
-- url     : https://prove2.me/theorems/fb43ec0b-7b31-4e7a-8a45-baaeef84504d
-- title:
--   Net aggregate deductible premium is nonnegative
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. The aggregate recovery and probability weights are each nonnegative, so their finite sum has nonnegative expected value. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   w_s\ge0\Longrightarrow \Pi_{\mathrm{agg}}\ge0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateDeductiblePremium_nonneg is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductiblePremium

namespace ActuarialValuation

theorem aggregateDeductiblePremium_nonneg
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ aggregateDeductiblePremium w x B n d := by sorry

end ActuarialValuation
