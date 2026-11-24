-- Prove2me | Theorems.Thm_ChromaticReconstruction_edgeFinset_PL
-- name    : ChromaticReconstruction.edgeFinset_PL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:49:03.218779+00:00
-- url     : https://prove2.me/theorems/0938aed5-5264-4495-86b0-50b7ba7f90ce
-- title:
--   Chromatic Reconstruction: edge Finset PL
-- statement:
--   The Chromatic Reconstruction construction uses the edge Finset PL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L93-L104
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L93-L104

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.edgeFinset_PL {n c : ℕ} (hc : c < n) :
    (PL n c).edgeFinset = insert (lf n c) ((range (n - 1)).image (pe n)) := by sorry
