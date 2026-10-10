-- Prove2me | Theorems.Thm_ActuarialValuation_dbHMRCMaximumCash_le_gross
-- name    : ActuarialValuation.dbHMRCMaximumCash_le_gross
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:26:32.277677+00:00
-- url     : https://prove2.me/theorems/c2e50409-d52f-4b37-83f0-98922a64e53e
-- title:
--   dbHMRCMaximumCash le gross
-- statement:
--   Original derived theorem for UK DB pension valuation. The HMRC-derived cash bound does not exceed the value of surrendering the entire original annual pension. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   L_{\max}\le fg
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash

namespace ActuarialValuation

theorem dbHMRCMaximumCash_le_gross (g f : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) : dbHMRCMaximumCash g f ≤ f * g := by sorry

end ActuarialValuation
