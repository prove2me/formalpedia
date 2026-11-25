-- Prove2me | Theorems.Thm_ChromaticReconstruction_leaf_val_PL
-- name    : ChromaticReconstruction.leaf_val_PL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:05:57.898081+00:00
-- url     : https://prove2.me/theorems/a536ac2c-b311-4aff-9bf0-bbc14ae037e0
-- title:
--   Chromatic Reconstruction: leaf val PL
-- statement:
--   The Chromatic Reconstruction construction uses the leaf val PL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L54-L58
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L54-L58

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.leaf_val_PL {n c : ℕ} (x : Fin (n + 1)) (hx : (PL n c).degree x ≤ 1) :
    x.val = 0 ∨ x.val + 1 = n ∨ x.val = n := by sorry
