-- Prove2me | Theorems.Thm_ActuarialValuation_dbCommutationHeadroom_mono
-- name    : ActuarialValuation.dbCommutationHeadroom_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:30:12.747851+00:00
-- url     : https://prove2.me/theorems/431f1700-9f8e-4ad0-b3ed-8c6709e026d0
-- title:
--   dbCommutationHeadroom mono
-- statement:
--   Original derived theorem for UK DB pension valuation. Increasing commuted cash monotonically reduces the available HMRC basic headroom. In the published mission the exact Lean binders and all positivity conditions determine the actuarial model. This proposition is a new derived finite or real-algebraic statement and is not asserted to be a numbered theorem in a pension statute.
--
--   Mathematical relation:
--
--   $$
--   L_1\le L_2\Longrightarrow H(L_2)\le H(L_1)
--   $$
-- source:
--   Original derived result. HMRC PTM063240 formula 20fg/(20+3f), 25% DB entitlement, LSA and separate tranche reductions. HMRC Pensions Tax Manual PTM063240 (updated 24 August 2026), defined-benefits PCLS applicable amount; Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 9, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm063240. Specific Lean statement is a new formal derivation, not a verbatim source theorem. Supporting exact source-page context: DB_Pension_Tax_Free_Cash.pdf, introductory scheme commutation model page 1; HMRC PTM063240 applicable amount online (not separately paginated)..

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutationHeadroom

namespace ActuarialValuation

theorem dbCommutationHeadroom_mono (g f L₁ L₂ : ℝ)
  (hf : 0 < f) (h : L₁ ≤ L₂) :
  dbCommutationHeadroom g L₂ f ≤ dbCommutationHeadroom g L₁ f := by sorry

end ActuarialValuation
