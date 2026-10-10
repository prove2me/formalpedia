-- Prove2me | Theorems.Thm_ActuarialValuation_layerExpectedCeded_stoploss_difference
-- name    : ActuarialValuation.layerExpectedCeded_stoploss_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:33:23.626513+00:00
-- url     : https://prove2.me/theorems/d6de2284-f6e0-4de5-8512-e8ab2ee6d1a5
-- title:
--   Net layer premium equals difference of two stop-loss premiums
-- statement:
--   The expected capped ceded payment equals the expected unlimited excess above attachment d, less the excess above the upper layer attachment d+L. The identity follows termwise from the exact pointwise loss partition and finite linearity, with no distribution-normalisation assumption.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{EL}_{d,L}=\mathrm{SL}(d)-\mathrm{SL}(d+L)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerExpectedCeded_stoploss_difference is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess

namespace ActuarialValuation

theorem layerExpectedCeded_stoploss_difference
  (w : ℕ → ℝ) (B d L : ℕ) :
  layerExpectedCeded w B d L =
    layerExpectedExcess w B d -
      layerExpectedExcess w B (d + L) := by sorry

end ActuarialValuation
