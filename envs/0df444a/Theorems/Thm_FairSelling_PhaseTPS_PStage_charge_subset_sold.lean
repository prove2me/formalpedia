-- Prove2me | Theorems.Thm_FairSelling_PhaseTPS_PStage_charge_subset_sold
-- name    : FairSelling.PhaseTPS.PStage.charge_subset_sold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:46:47.986805+00:00
-- url     : https://prove2.me/theorems/fb4ae80c-20fd-4f5a-9bd1-2123dc210d1b
-- title:
--   PStage: charge subset sold
-- statement:
--   The PStage construction uses the charge subset sold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L351-L352
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefxPhase.lean#L351-L352

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]

theorem FairSelling.PhaseTPS.PStage.charge_subset_sold (s : PStage G n) (i : Fin n) : s.charge i ⊆ s.sold := by sorry
