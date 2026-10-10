-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_zero_limit
-- name    : ActuarialValuation.layerCededPayment_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:34.814975+00:00
-- url     : https://prove2.me/theorems/e3c63df2-22ae-4bd7-bd56-98304433c92b
-- title:
--   A zero-width layer has no payment
-- statement:
--   A reinsurance layer with zero contractual limit cannot reimburse any amount. The minimum of the claim excess and zero is zero for every loss and attachment.
--
--   **Mathematical statement**
--
--   $$
--   C_{d,0}(x)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_zero_limit is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerCededPayment_zero_limit (x d : ℕ) :
  layerCededPayment x d 0 = 0 := by sorry

end ActuarialValuation
