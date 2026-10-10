-- Prove2me | Theorems.Thm_ActuarialValuation_layerExpectedCeded_monotone
-- name    : ActuarialValuation.layerExpectedCeded_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:33:01.392981+00:00
-- url     : https://prove2.me/theorems/8356b70a-07ad-4652-96ec-c5cd88294ce4
-- title:
--   More layer width weakly increases net expected ceded loss
-- statement:
--   Each claim's ceded payment under limit L1 is no greater than under L2. Under nonnegative loss weights, multiplying and summing retains the pointwise order, so the larger layer's expected ceded loss cannot decrease.
--
--   **Mathematical statement**
--
--   $$
--   L_1\le L_2\Rightarrow\mathrm{EL}_{d,L_1}\le\mathrm{EL}_{d,L_2}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 21, Section 21.10, printed page 389 (Library PDF page 415), parent framework: Equations (21.10)–(21.12), Example 21.4. Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://www.gov.uk/hmrc-internal-manuals/general-insurance-manual/gim8080. The specific Lean declaration ActuarialValuation.layerExpectedCeded_monotone is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerExpectedCeded
import Definitions.Def_actuarial_layerCededPayment

namespace ActuarialValuation

theorem layerExpectedCeded_monotone
  (w : ℕ → ℝ) (B d L1 L2 : ℕ)
  (hw : ∀ x, 0 ≤ w x) (h : L1 ≤ L2) :
  layerExpectedCeded w B d L1 ≤ layerExpectedCeded w B d L2 := by sorry

end ActuarialValuation
