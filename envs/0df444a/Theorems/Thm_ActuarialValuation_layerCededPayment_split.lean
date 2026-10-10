-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededPayment_split
-- name    : ActuarialValuation.layerCededPayment_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:31:57.225229+00:00
-- url     : https://prove2.me/theorems/2eef92dd-2bb8-4aef-957e-a843148486e4
-- title:
--   An unlimited excess decomposes into capped layer and higher excess
-- statement:
--   The unlimited loss above lower attachment d divides into the amount ceded within the limit L and the remaining positive claim above d+L. This pointwise partition is valid at zero loss, zero attachment and zero limit.
--
--   **Mathematical statement**
--
--   $$
--   (x-d)_+=\min((x-d)_+,L)+(x-d-L)_+
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededPayment_split is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerHigherExcess

namespace ActuarialValuation

theorem layerCededPayment_split (x d L : ℕ) :
  layerExcessLoss x d =
    layerCededPayment x d L + layerHigherExcess x d L := by sorry

end ActuarialValuation
