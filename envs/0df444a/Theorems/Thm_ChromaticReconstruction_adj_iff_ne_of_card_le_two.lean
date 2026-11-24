-- Prove2me | Theorems.Thm_ChromaticReconstruction_adj_iff_ne_of_card_le_two
-- name    : ChromaticReconstruction.adj_iff_ne_of_card_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:34:15.302799+00:00
-- url     : https://prove2.me/theorems/5d8a0159-9c25-4f74-8a32-1fa55f51ecab
-- title:
--   Chromatic Reconstruction: adj iff ne of card le two
-- statement:
--   The Chromatic Reconstruction construction uses the adj iff ne of card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L198-L212
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L198-L212

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}

theorem ChromaticReconstruction.adj_iff_ne_of_card_le_two (hS : S.Connected) (hk : Fintype.card K ≤ 2) {x y : K} :
    S.Adj x y ↔ x ≠ y := by sorry
