-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateDeductibleCeded_monotone_deductible
-- name    : ActuarialValuation.aggregateDeductibleCeded_monotone_deductible
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:45:20.470983+00:00
-- url     : https://prove2.me/theorems/92152885-610f-4b27-aba3-cbff587bc882
-- title:
--   A larger aggregate deductible reduces ceded claim amount
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. Increasing the insurer's annual aggregate retention cannot increase the amount reimbursed by the reinsurer. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   d_1\le d_2\Longrightarrow C_{\mathrm{agg}}(d_2)\le C_{\mathrm{agg}}(d_1)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateDeductibleCeded_monotone_deductible is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateDeductibleCeded

namespace ActuarialValuation

theorem aggregateDeductibleCeded_monotone_deductible
  (x : ℕ → ℕ) (n d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
  aggregateDeductibleCeded x n d₂ ≤ aggregateDeductibleCeded x n d₁ := by sorry

end ActuarialValuation
