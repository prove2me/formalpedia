-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_within
-- name    : ActuarialValuation.layerCededPayment_within
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:39.392452+00:00
-- url     : https://prove2.me/theorems/fe8ea420-d7ce-4e96-98a5-e079235fc85c
-- title:
--   Within the layer the ceded claim equals all excess above attachment
-- statement:
--   For a claim no greater than the upper layer attachment, its excess over d is at most the layer limit. The capped payment therefore equals the entire positive excess, including claims below attachment where both values are zero.
--
--   **Mathematical statement**
--
--   $$
--   x\le d+L\Rightarrow C_{d,L}(x)=E_d(x)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_within is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

theorem layerCededPayment_within (x d L : ℕ)
  (h : x ≤ d + L) :
  layerCededPayment x d L = layerExcessLoss x d := by sorry

end ActuarialValuation
