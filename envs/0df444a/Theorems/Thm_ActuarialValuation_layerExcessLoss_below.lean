-- Prove2me | Theorems.Thm_ActuarialValuation_layerExcessLoss_below
-- name    : ActuarialValuation.layerExcessLoss_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:30:01.791663+00:00
-- url     : https://prove2.me/theorems/f78f0edf-8046-42a2-9fcf-795ef980a0b2
-- title:
--   Claim below or at attachment has no excess
-- statement:
--   When the claim amount does not exceed the attachment, no monetary loss lies above the retention. Saturating natural-number subtraction gives zero excess exactly.
--
--   **Mathematical statement**
--
--   $$
--   x\le d\Rightarrow E_d(x)=0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerExcessLoss_below is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

theorem layerExcessLoss_below (x d : ℕ) (h : x ≤ d) :
  layerExcessLoss x d = 0 := by sorry

end ActuarialValuation
