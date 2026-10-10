-- Prove2me | Theorems.Thm_ActuarialValuation_layerExpectedCeded_le_full_stoploss
-- name    : ActuarialValuation.layerExpectedCeded_le_full_stoploss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:33:47.403982+00:00
-- url     : https://prove2.me/theorems/57911e7a-5932-46c1-a27b-8640891dec7e
-- title:
--   Layered ceded cost cannot exceed uncapped stop-loss at the same attachment
-- statement:
--   The capped ceded payment is at most the unlimited positive excess for every underlying claim. Nonnegative claim probabilities therefore make the net ceded cost no greater than the original unlimited stop-loss premium.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{EL}_{d,L}\le\mathrm{SL}(d)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerExpectedCeded_le_full_stoploss is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerExpectedCeded_le_full_stoploss
  (w : ℕ → ℝ) (B d L : ℕ) (hw : ∀ x, 0 ≤ w x) :
  layerExpectedCeded w B d L ≤ layerExpectedExcess w B d := by sorry

end ActuarialValuation
