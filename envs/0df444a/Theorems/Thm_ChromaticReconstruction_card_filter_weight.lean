-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_filter_weight
-- name    : ChromaticReconstruction.card_filter_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:27:47.501235+00:00
-- url     : https://prove2.me/theorems/ec5fbfce-d63f-465f-af29-b6d89536d4e3
-- title:
--   Chromatic Reconstruction: card filter weight
-- statement:
--   The Chromatic Reconstruction construction uses the card filter weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L119-L123
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L119-L123

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]

theorem ChromaticReconstruction.card_filter_weight (w : K → ℕ) (a : ℕ) :
    #{x | w x = a} = Multiset.count a (wts w) := by sorry
