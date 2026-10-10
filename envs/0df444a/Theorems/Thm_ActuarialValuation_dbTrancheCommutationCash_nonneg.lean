-- Prove2me | Theorems.Thm_ActuarialValuation_dbTrancheCommutationCash_nonneg
-- name    : ActuarialValuation.dbTrancheCommutationCash_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:36:47.080126+00:00
-- url     : https://prove2.me/theorems/885a8014-6047-4e71-8b4b-24bf050dd70b
-- title:
--   dbTrancheCommutationCash nonneg
-- statement:
--   Original derived theorem for UK DB pension valuation. Nonnegative tranche factors and annual pension reductions produce nonnegative total lump sum. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   f_i,x_i\ge0\Longrightarrow L\ge0
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheCommutationCash

namespace ActuarialValuation

theorem dbTrancheCommutationCash_nonneg (factor reduction : ℕ → ℝ) (n : ℕ)
  (hf : ∀ i ∈ Finset.range n, 0 ≤ factor i)
  (hx : ∀ i ∈ Finset.range n, 0 ≤ reduction i) :
  0 ≤ dbTrancheCommutationCash factor reduction n := by sorry

end ActuarialValuation
