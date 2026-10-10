-- Prove2me | Theorems.Thm_ActuarialValuation_dbPCLSMaximum_fundamental
-- name    : ActuarialValuation.dbPCLSMaximum_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:37:07.946882+00:00
-- url     : https://prove2.me/theorems/167b87b3-129b-41c2-ab13-d249c1b832e9
-- title:
--   dbPCLSMaximum fundamental
-- statement:
--   Original derived theorem for UK DB pension valuation. The capstone proves the attained basic HMRC cash limit, verifies the allowance-limited cash remains admissible, and retains a nonnegative pension tax headroom. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   H(L_{\max})=0,\quad0\le L_{\rm cap}\le\min(L_{\max},A),\quad H(L_{\rm cap})\ge0
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom
import Definitions.Def_actuarial_dbCappedPCLS

namespace ActuarialValuation

theorem dbPCLSMaximum_fundamental (g f A : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) (hA : 0 ≤ A) :
  (dbCommutationHeadroom g (dbHMRCMaximumCash g f) f = 0) ∧
  (0 ≤ dbCappedPCLS g f A) ∧
  (dbCappedPCLS g f A ≤ dbHMRCMaximumCash g f) ∧
  (dbCappedPCLS g f A ≤ A) ∧
  (0 ≤ dbCommutationHeadroom g (dbCappedPCLS g f A) f) := by sorry

end ActuarialValuation
