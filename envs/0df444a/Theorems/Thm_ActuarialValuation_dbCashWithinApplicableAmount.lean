-- Prove2me | Theorems.Thm_ActuarialValuation_dbCashWithinApplicableAmount
-- name    : ActuarialValuation.dbCashWithinApplicableAmount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:30:32.966099+00:00
-- url     : https://prove2.me/theorems/93cc9abb-fbde-4764-898c-a5dc8b4fb89b
-- title:
--   dbCashWithinApplicableAmount
-- statement:
--   Original derived theorem for UK DB pension valuation. The exact basic HMRC upper limit is equivalent to the algebraic maximum cash formula, under its explicit simplified assumptions. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   3L\le20P_B\iff L\le20fg/(20+3f)
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom

namespace ActuarialValuation

theorem dbCashWithinApplicableAmount (g f L : ℝ)
  (hf : 0 < f) :
  (dbCommutationHeadroom g L f ≥ 0 ↔ L ≤ dbHMRCMaximumCash g f) := by sorry

end ActuarialValuation
