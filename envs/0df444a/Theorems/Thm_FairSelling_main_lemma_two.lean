-- Prove2me | Theorems.Thm_FairSelling_main_lemma_two
-- name    : FairSelling.main_lemma_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:05.87455+00:00
-- url     : https://prove2.me/theorems/08026ac1-b611-4cd7-a3d0-9c2581f2217d
-- title:
--   Fair Selling: main lemma two
-- statement:
--   The Fair Selling construction uses the main lemma two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L524-L534
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L524-L534

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.main_lemma_two (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (B : Finset G) (hloss : MainLemmaTwoLoss w p B) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by sorry
