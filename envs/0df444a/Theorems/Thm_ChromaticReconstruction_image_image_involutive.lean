-- Prove2me | Theorems.Thm_ChromaticReconstruction_image_image_involutive
-- name    : ChromaticReconstruction.image_image_involutive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:00:02.938251+00:00
-- url     : https://prove2.me/theorems/1cabc530-9428-4ebd-9a8f-edb0d4dc9a1f
-- title:
--   Chromatic Reconstruction: image image involutive
-- statement:
--   The Chromatic Reconstruction construction uses the image image involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L56-L60
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L56-L60

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.image_image_involutive {α : Type*} [DecidableEq α] {f : α → α} (hf : Function.Involutive f)
    (F : Finset (Sym2 α)) : (F.image (Sym2.map f)).image (Sym2.map f) = F := by sorry
