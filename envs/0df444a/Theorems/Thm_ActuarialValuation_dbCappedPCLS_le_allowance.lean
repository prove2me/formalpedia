-- Prove2me | Theorems.Thm_ActuarialValuation_dbCappedPCLS_le_allowance
-- name    : ActuarialValuation.dbCappedPCLS_le_allowance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:32:10.707958+00:00
-- url     : https://prove2.me/theorems/cc1f5d46-752b-4b1a-b130-5a4f5c6d5093
-- title:
--   dbCappedPCLS le allowance
-- statement:
--   Original derived theorem for UK DB pension valuation. The paid cash cannot exceed the externally supplied available allowance. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   L_{\rm cap}\le A
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCappedPCLS

namespace ActuarialValuation

theorem dbCappedPCLS_le_allowance (g f A : ℝ) :
  dbCappedPCLS g f A ≤ A := by sorry

end ActuarialValuation
