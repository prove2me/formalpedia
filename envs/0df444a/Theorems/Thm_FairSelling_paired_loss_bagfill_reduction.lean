-- Prove2me | Theorems.Thm_FairSelling_paired_loss_bagfill_reduction
-- name    : FairSelling.paired_loss_bagfill_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:13.369318+00:00
-- url     : https://prove2.me/theorems/a3b4eecd-7066-4233-b117-121129f12540
-- title:
--   Fair Selling: paired loss bagfill reduction
-- statement:
--   The Fair Selling construction uses the paired loss bagfill reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L487-L503
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L487-L503

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.paired_loss_bagfill_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R C : Finset G) (hC : C ⊆ R)
    (hClo : (3/4) * MMS 3 w p ≤ vbarSum w p C)
    (hChi : vbarSum w p C ≤ MMS 3 w p)
    (hR : MMS 3 w p + (3/4) * MMS 3 w p ≤ vbarSum w p R) :
    (3/4) * MMS 3 w p ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by sorry
