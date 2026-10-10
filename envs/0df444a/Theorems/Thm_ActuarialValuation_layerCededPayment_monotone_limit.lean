-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_monotone_limit
-- name    : ActuarialValuation.layerCededPayment_monotone_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:07.28699+00:00
-- url     : https://prove2.me/theorems/d38f7465-fbcd-4080-ad77-76b09530fbdb
-- title:
--   Increasing layer limit cannot reduce ceded payment
-- statement:
--   At a fixed claim and retention, increasing available layer width can only expand the reimbursable part of the claim's positive excess. The ceded amount therefore increases or stays unchanged.
--
--   **Mathematical statement**
--
--   $$
--   L_1\le L_2\Rightarrow C_{d,L_1}(x)\le C_{d,L_2}(x)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_monotone_limit is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerCededPayment_monotone_limit
  (x d L1 L2 : ℕ) (h : L1 ≤ L2) :
  layerCededPayment x d L1 ≤ layerCededPayment x d L2 := by sorry

end ActuarialValuation
