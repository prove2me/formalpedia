-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductibleCeded_zero_attachment
-- name    : ActuarialValuation.perClaimDeductibleCeded_zero_attachment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:44:53.312507+00:00
-- url     : https://prove2.me/theorems/5efd5a7c-e62e-48ee-b286-5185db4fab1c
-- title:
--   Zero per-occurrence deductible cedes every claim
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. With each individual deductible set to zero, the summed per-claim recovery equals the gross aggregate. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{individual}}(0)=S_n
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductibleCeded_zero_attachment is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

theorem perClaimDeductibleCeded_zero_attachment (x : ℕ → ℕ) (n : ℕ) :
  perClaimDeductibleCeded x n 0 = aggregateLossTotal x n := by sorry

end ActuarialValuation
