-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateDeductibleCeded_le_total
-- name    : ActuarialValuation.aggregateDeductibleCeded_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:44:14.772399+00:00
-- url     : https://prove2.me/theorems/284cca11-f676-4da0-ac6f-f8140cabe7e9
-- title:
--   Aggregate reinsurance cannot exceed gross claims
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Natural-number positive part prevents annual aggregate cover from paying more than the underlying total insured claims. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{agg}}\le S_n
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateDeductibleCeded_le_total is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal
import Definitions.Def_actuarial_aggregateDeductibleCeded

namespace ActuarialValuation

theorem aggregateDeductibleCeded_le_total (x : ℕ → ℕ) (n d : ℕ) :
  aggregateDeductibleCeded x n d ≤ aggregateLossTotal x n := by sorry

end ActuarialValuation
