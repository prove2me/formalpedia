-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateDeductibleCeded_below
-- name    : ActuarialValuation.aggregateDeductibleCeded_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:43:31.046359+00:00
-- url     : https://prove2.me/theorems/8e59d992-497a-4c00-905f-3f084fa8f0c3
-- title:
--   No aggregate cover attaches when total claims are below deductible
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Where the sum of all covered claims does not exceed the annual deductible, no aggregate recovery is paid. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   S_n\le d\Longrightarrow C_{\mathrm{agg}}=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateDeductibleCeded_below is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal
import Definitions.Def_actuarial_aggregateDeductibleCeded

namespace ActuarialValuation

theorem aggregateDeductibleCeded_below (x : ℕ → ℕ) (n d : ℕ)
  (h : aggregateLossTotal x n ≤ d) :
  aggregateDeductibleCeded x n d = 0 := by sorry

end ActuarialValuation
