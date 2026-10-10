-- Prove2me | Theorems.Thm_ActuarialValuation_layerExpectedCeded_nonneg
-- name    : ActuarialValuation.layerExpectedCeded_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:32:34.161535+00:00
-- url     : https://prove2.me/theorems/fdfbf9f0-3691-42f3-967e-66af5bf344fa
-- title:
--   Ceded layer expected loss cannot be negative with nonnegative mass
-- statement:
--   Every claim-layer payment is a nonnegative natural amount, and all probability coefficients are nonnegative. The finite weighted expected ceded cost is consequently nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   w_x\ge0\Rightarrow \mathrm{EL}_{d,L}\ge0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerExpectedCeded_nonneg is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerExpectedCeded_nonneg
  (w : ℕ → ℝ) (B d L : ℕ) (hw : ∀ x, 0 ≤ w x) :
  0 ≤ layerExpectedCeded w B d L := by sorry

end ActuarialValuation
