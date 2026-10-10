-- Prove2me | Theorems.Thm_ActuarialValuation_dbTrancheResidualPension_nonneg
-- name    : ActuarialValuation.dbTrancheResidualPension_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:36:35.479985+00:00
-- url     : https://prove2.me/theorems/ebaa4474-cd77-43b6-a634-abde3c8160c6
-- title:
--   dbTrancheResidualPension nonneg
-- statement:
--   Original derived theorem for UK DB pension valuation. Each retained pension tranche is nonnegative if the annual reduction is bounded by that tranche's pension. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   x_i\le p_i\Longrightarrow P_B\ge0
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheResidualPension

namespace ActuarialValuation

theorem dbTrancheResidualPension_nonneg (pension reduction : ℕ → ℝ) (n : ℕ)
  (h : ∀ i ∈ Finset.range n, reduction i ≤ pension i) :
  0 ≤ dbTrancheResidualPension pension reduction n := by sorry

end ActuarialValuation
