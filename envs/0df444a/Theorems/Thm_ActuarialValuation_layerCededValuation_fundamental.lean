-- Prove2me | Theorems.Thm_ActuarialValuation_layerCededValuation_fundamental
-- name    : ActuarialValuation.layerCededValuation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:34:08.233982+00:00
-- url     : https://prove2.me/theorems/076e2330-ff5b-4487-aede-b54baf67d657
-- title:
--   Layer payment decomposition and actuarially exact stop-loss difference
-- statement:
--   The capstone unifies a bounded single-claim excess-of-loss treaty's payment decomposition with the exact net layer premium as difference of two unlimited stop-loss premiums, and establishes its nonnegative bound against gross excess. It does not assert an expense-loaded reinsurance price or infinite-support integration.
--
--   **Mathematical statement**
--
--   $$
--   E_d(x)=C_{d,L}(x)+H_{d,L}(x),\quad \mathrm{EL}_{d,L}=\mathrm{SL}(d)-\mathrm{SL}(d+L)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerCededValuation_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExcessLoss
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerHigherExcess
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerExpectedExcess

namespace ActuarialValuation

theorem layerCededValuation_fundamental
  (w : ℕ → ℝ) (B x d L : ℕ)
  (hw : ∀ k, 0 ≤ w k) :
  (layerExcessLoss x d =
    layerCededPayment x d L + layerHigherExcess x d L) ∧
  (layerExpectedCeded w B d L =
    layerExpectedExcess w B d -
      layerExpectedExcess w B (d + L)) ∧
  (0 ≤ layerExpectedCeded w B d L ∧
    layerExpectedCeded w B d L ≤ layerExpectedExcess w B d) := by sorry

end ActuarialValuation
