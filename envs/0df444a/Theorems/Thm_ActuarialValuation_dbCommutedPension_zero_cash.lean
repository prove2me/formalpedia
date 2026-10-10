-- Prove2me | Theorems.Thm_ActuarialValuation_dbCommutedPension_zero_cash
-- name    : ActuarialValuation.dbCommutedPension_zero_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:25:53.250978+00:00
-- url     : https://prove2.me/theorems/c30a8071-8458-4359-9829-8dfbebb6a995
-- title:
--   dbCommutedPension zero cash
-- statement:
--   Original derived theorem for UK DB pension valuation. If no pension is commuted, the original annual DB pension remains unchanged. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   L=0\Longrightarrow P_B=g
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutedPension

namespace ActuarialValuation

theorem dbCommutedPension_zero_cash (g f : ℝ) :
  dbCommutedPension g 0 f = g := by sorry

end ActuarialValuation
