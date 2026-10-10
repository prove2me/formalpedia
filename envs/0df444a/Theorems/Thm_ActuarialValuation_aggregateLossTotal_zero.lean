-- Prove2me | Theorems.Thm_ActuarialValuation_aggregateLossTotal_zero
-- name    : ActuarialValuation.aggregateLossTotal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:43:17.231412+00:00
-- url     : https://prove2.me/theorems/01d875ea-73a7-4336-a3de-28e31a44edb0
-- title:
--   An empty treaty portfolio has zero gross claims
-- statement:
--   This is an original derived actuarial theorem, based on the aggregate treaty compared with per occurrence excess-of-loss. An empty collection of claims has zero gross claims and therefore defines the base case for deductible comparisons. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   S_0=0
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 389 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: HMRC GIM8060, individual versus aggregate non-proportional reinsurance, supporting source https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8060. The Lean declaration ActuarialValuation.aggregateLossTotal_zero is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal

namespace ActuarialValuation

theorem aggregateLossTotal_zero (x : ℕ → ℕ) :
  aggregateLossTotal x 0 = 0 := by sorry

end ActuarialValuation
