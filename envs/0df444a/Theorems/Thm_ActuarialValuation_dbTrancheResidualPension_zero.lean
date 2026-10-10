-- Prove2me | Theorems.Thm_ActuarialValuation_dbTrancheResidualPension_zero
-- name    : ActuarialValuation.dbTrancheResidualPension_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:36:22.667179+00:00
-- url     : https://prove2.me/theorems/544b570b-3803-4414-b305-a345c9ce505e
-- title:
--   dbTrancheResidualPension zero
-- statement:
--   Original derived theorem for UK DB pension valuation. With no accrued tranches there is no residual scheme pension. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   P_B(0)=0
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheResidualPension

namespace ActuarialValuation

theorem dbTrancheResidualPension_zero (pension reduction : ℕ → ℝ) :
  dbTrancheResidualPension pension reduction 0 = 0 := by sorry

end ActuarialValuation
