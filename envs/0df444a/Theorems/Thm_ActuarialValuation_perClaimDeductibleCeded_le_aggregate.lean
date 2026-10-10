-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductibleCeded_le_aggregate
-- name    : ActuarialValuation.perClaimDeductibleCeded_le_aggregate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:45:38.604543+00:00
-- url     : https://prove2.me/theorems/97510335-a32f-4454-97cc-b67f3e087329
-- title:
--   Aggregate excess reimbursement dominates separate per-occurrence cover
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Under the same deductible d, charging the retention once to the portfolio never yields less ceded recovery than charging it separately against every claim. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \sum_{i<n}(x_i-d)_+\le (\sum_{i<n}x_i-d)_+
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductibleCeded_le_aggregate is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

theorem perClaimDeductibleCeded_le_aggregate
  (x : ℕ → ℕ) (n d : ℕ) :
  perClaimDeductibleCeded x n d ≤ aggregateDeductibleCeded x n d := by sorry

end ActuarialValuation
