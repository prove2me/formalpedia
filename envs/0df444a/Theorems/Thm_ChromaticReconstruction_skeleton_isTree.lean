-- Prove2me | Theorems.Thm_ChromaticReconstruction_skeleton_isTree
-- name    : ChromaticReconstruction.skeleton_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:28.476879+00:00
-- url     : https://prove2.me/theorems/fb4c9709-ea73-44e0-8a0f-aaf4eb353b08
-- title:
--   Chromatic Reconstruction: skeleton is Tree
-- statement:
--   The skeleton of a proper tree is a tree.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/ProperTree.lean#L157-L184
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/ProperTree.lean#L157-L184

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}

theorem ChromaticReconstruction.skeleton_isTree (hT : IsProperTree T) : (skeleton T).IsTree := by sorry
