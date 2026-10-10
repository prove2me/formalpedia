-- Prove2me | Theorems.Thm_ActuarialValuation_dbCommutationHeadroom_max_zero
-- name    : ActuarialValuation.dbCommutationHeadroom_max_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:26:48.09212+00:00
-- url     : https://prove2.me/theorems/851b9f6a-f515-4b50-9507-2ef0d02f7e7d
-- title:
--   dbCommutationHeadroom max zero
-- statement:
--   Original derived theorem for UK DB pension valuation. At the basic allowable amount, the HMRC commutation inequality binds exactly. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   H(L_{\max})=0
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom

namespace ActuarialValuation

theorem dbCommutationHeadroom_max_zero (g f : ℝ) (hf : 0 < f) :
  dbCommutationHeadroom g (dbHMRCMaximumCash g f) f = 0 := by sorry

end ActuarialValuation
