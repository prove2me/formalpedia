-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductiblePremium_le_aggregate
-- name    : ActuarialValuation.perClaimDeductiblePremium_le_aggregate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:26.898423+00:00
-- url     : https://prove2.me/theorems/cff1fbf2-d9d2-4a93-9239-3a3b216e7b51
-- title:
--   Expected per-claim reinsurance cost is bounded by aggregate deductible cost
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Pointwise coverage domination extends to the finite actuarial pure premiums under nonnegative scenario probability weights. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   w_s\ge0\Longrightarrow \Pi_{\mathrm{individual}}\le\Pi_{\mathrm{agg}}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductiblePremium_le_aggregate is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductiblePremium
import Definitions.Def_actuarial_perClaimDeductiblePremium

namespace ActuarialValuation

theorem perClaimDeductiblePremium_le_aggregate
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  perClaimDeductiblePremium w x B n d ≤
    aggregateDeductiblePremium w x B n d := by sorry

end ActuarialValuation
