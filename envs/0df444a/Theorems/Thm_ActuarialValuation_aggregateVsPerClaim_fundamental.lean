-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateVsPerClaim_fundamental
-- name    : ActuarialValuation.aggregateVsPerClaim_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:40.503427+00:00
-- url     : https://prove2.me/theorems/68158091-1159-465e-bd71-2ae053be2c25
-- title:
--   Aggregate-versus-per-occurrence deductible valuation capstone
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. The capstone joins the nontrivial pointwise reinsurance coverage inequality to the same ordering of expected pure premiums, without conflating a whole-year treaty with a per-claim deductible. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   C_{\mathrm{individual}}\le C_{\mathrm{agg}},\quad0\le\Pi_{\mathrm{agg}},\quad\Pi_{\mathrm{individual}}\le\Pi_{\mathrm{agg}}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateVsPerClaim_fundamental is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded
import Definitions.Def_actuarial_perClaimDeductibleCeded
import Definitions.Def_actuarial_aggregateDeductiblePremium
import Definitions.Def_actuarial_perClaimDeductiblePremium

namespace ActuarialValuation

theorem aggregateVsPerClaim_fundamental
  (w : ℕ → ℝ) (x : ℕ → ℕ → ℕ) (B n d : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  (perClaimDeductibleCeded (x 0) n d ≤
    aggregateDeductibleCeded (x 0) n d) ∧
  (0 ≤ aggregateDeductiblePremium w x B n d) ∧
  (perClaimDeductiblePremium w x B n d ≤
    aggregateDeductiblePremium w x B n d) := by sorry

end ActuarialValuation
