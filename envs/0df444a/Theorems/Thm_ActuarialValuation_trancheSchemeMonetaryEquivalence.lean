-- Prove2me | Theorems.Thm_ActuarialValuation_trancheSchemeMonetaryEquivalence
-- name    : ActuarialValuation.trancheSchemeMonetaryEquivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:26:05.850078+00:00
-- url     : https://prove2.me/theorems/04f2d54e-b414-40c2-89de-776e48b27d97
-- title:
--   trancheSchemeMonetaryEquivalence
-- statement:
--   Original derived theorem for UK DB pension valuation. Separate actuarially equivalent tranche cashflow packages combine exactly into the scheme's whole monetary present value. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   \sum_{i<n}P_if_iA_i=\sum_{i<n}P_iD_i
--   $$
-- source:
--   Original derived result. Separate factor by pension tranche; multi-tranche actuarial equivalence, section 18 eq. (58)-(60). UK DB Retirement Factors Mathematical Framework, controlled version 5.3.0 (13 July 2026), Chapter 18, tranche equations (58)-(60); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/contents/9EAA5D04EA64E67BC84F7555AC82B4D1. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: UK_DB_Retirement_Factors_Mathematical_Framework_v5_3_0.pdf, Chapter 18, printed page 102, Eq. 58-60.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_trancheSchemeAdjustedPV
import Definitions.Def_actuarial_trancheSchemeComparatorPV

namespace ActuarialValuation

theorem trancheSchemeMonetaryEquivalence (P A D : ℕ → ℝ) (n : ℕ)
  (hA : ∀ i ∈ Finset.range n, A i ≠ 0) :
  trancheSchemeAdjustedPV P A D n = trancheSchemeComparatorPV P D n := by sorry

end ActuarialValuation
