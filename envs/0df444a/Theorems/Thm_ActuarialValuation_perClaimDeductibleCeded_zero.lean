-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductibleCeded_zero
-- name    : ActuarialValuation.perClaimDeductibleCeded_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:43:45.144901+00:00
-- url     : https://prove2.me/theorems/c528fbc0-adb9-4f12-bdab-f86674535c97
-- title:
--   An empty portfolio has zero per-claim ceded payments
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. There are no claim occurrences to which a deductible can be applied when the annual claim count is zero. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{individual}}(0,d)=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductibleCeded_zero is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

theorem perClaimDeductibleCeded_zero (x : ℕ → ℕ) (d : ℕ) :
  perClaimDeductibleCeded x 0 d = 0 := by sorry

end ActuarialValuation
