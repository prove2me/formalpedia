-- Prove2me | Theorems.Thm_ActuarialValuation_perClaimDeductibleCeded_below
-- name    : ActuarialValuation.perClaimDeductibleCeded_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:43:58.419098+00:00
-- url     : https://prove2.me/theorems/2d7b4020-6aa4-414c-a5b6-06b4340392e6
-- title:
--   No individual recovery if all claims are below deductible
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Every separate excess claim payment vanishes if each covered claim is individually at most the retention. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   (\forall i<n:x_i\le d)\Longrightarrow C_{\mathrm{individual}}=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.perClaimDeductibleCeded_below is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_perClaimDeductibleCeded

namespace ActuarialValuation

theorem perClaimDeductibleCeded_below (x : ℕ → ℕ) (n d : ℕ)
  (h : ∀ i ∈ Finset.range n, x i ≤ d) :
  perClaimDeductibleCeded x n d = 0 := by sorry

end ActuarialValuation
