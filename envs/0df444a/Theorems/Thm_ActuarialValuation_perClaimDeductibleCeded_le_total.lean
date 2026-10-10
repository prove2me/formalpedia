-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductibleCeded_le_total
-- name    : ActuarialValuation.perClaimDeductibleCeded_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:44:28.185984+00:00
-- url     : https://prove2.me/theorems/0e3b0156-a4cd-4a1c-a48b-166a25a84231
-- title:
--   Combined per-claim recovery cannot exceed gross claims
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Summing individually capped excess claims cannot create reimbursement greater than all the underlying gross claim amounts. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{individual}}\le S_n
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductibleCeded_le_total is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

theorem perClaimDeductibleCeded_le_total (x : ℕ → ℕ) (n d : ℕ) :
  perClaimDeductibleCeded x n d ≤ aggregateLossTotal x n := by sorry

end ActuarialValuation
