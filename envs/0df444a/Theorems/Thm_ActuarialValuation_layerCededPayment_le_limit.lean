-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_le_limit
-- name    : ActuarialValuation.layerCededPayment_le_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:47.327818+00:00
-- url     : https://prove2.me/theorems/247a21dd-09e6-4e36-a49b-cb984872ee26
-- title:
--   Ceded amount never exceeds the treaty limit
-- statement:
--   The reinsurance layer's payment is the smaller of the claim's positive excess and its maximum contractual width. Therefore no loss scenario produces an insurer reimbursement greater than the limit.
--
--   **Mathematical statement**
--
--   $$
--   C_{d,L}(x)\le L
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_le_limit is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerCededPayment_le_limit (x d L : ℕ) :
  layerCededPayment x d L ≤ L := by sorry

end ActuarialValuation
