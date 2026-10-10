-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_below
-- name    : ActuarialValuation.layerCededPayment_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:16.200073+00:00
-- url     : https://prove2.me/theorems/3d6e0780-8b7a-4ce9-8511-7c192f7d1135
-- title:
--   No reinsurance claim is payable below attachment
-- statement:
--   A capped reinsurance layer cannot trigger before the claim exceeds its attachment. Its ceded amount is zero regardless of the available limit.
--
--   **Mathematical statement**
--
--   $$
--   x\le d\Rightarrow C_{d,L}(x)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_below is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

theorem layerCededPayment_below (x d L : ℕ) (h : x ≤ d) :
  layerCededPayment x d L = 0 := by sorry

end ActuarialValuation
