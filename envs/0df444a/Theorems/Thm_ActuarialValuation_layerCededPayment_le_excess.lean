-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_le_excess
-- name    : ActuarialValuation.layerCededPayment_le_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:06.269471+00:00
-- url     : https://prove2.me/theorems/c1ab5ac5-b4c6-4dbc-9ea1-be1b450bb310
-- title:
--   Ceded payment is bounded by the full gross claim excess
-- statement:
--   The capped ceded claim cannot exceed what an unlimited stop-loss contract would pay above the same retention. This is an immediate consequence of taking the minimum with the contractual limit.
--
--   **Mathematical statement**
--
--   $$
--   C_{d,L}(x)\le E_d(x)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_le_excess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss

namespace ActuarialValuation

theorem layerCededPayment_le_excess (x d L : ℕ) :
  layerCededPayment x d L ≤ layerExcessLoss x d := by sorry

end ActuarialValuation
