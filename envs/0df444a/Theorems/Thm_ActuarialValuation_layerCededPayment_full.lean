-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_full
-- name    : ActuarialValuation.layerCededPayment_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:27.804738+00:00
-- url     : https://prove2.me/theorems/4046b0c2-a3c3-4229-91cc-86b80c0fae54
-- title:
--   If claim reaches the layer top, reimbursement is exactly the limit
-- statement:
--   Where the gross claim reaches or exceeds the attachment plus layer width, the positive excess contains at least the entire layer. The insurer receives its full layer limit, with further claim losses borne elsewhere.
--
--   **Mathematical statement**
--
--   $$
--   x\ge d+L\Rightarrow C_{d,L}(x)=L
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_full is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerCededPayment_full (x d L : ℕ)
  (h : d + L ≤ x) :
  layerCededPayment x d L = L := by sorry

end ActuarialValuation
