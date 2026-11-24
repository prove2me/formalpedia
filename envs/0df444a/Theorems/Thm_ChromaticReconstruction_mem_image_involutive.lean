-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_image_involutive
-- name    : ChromaticReconstruction.mem_image_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:58:04.539369+00:00
-- url     : https://prove2.me/theorems/0d2b3ecc-c83c-4b1c-b534-a3f4e0e5f449
-- title:
--   Chromatic Reconstruction: mem image involutive
-- statement:
--   The Chromatic Reconstruction construction uses the mem image involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L47-L54
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L47-L54

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.mem_image_involutive {α : Type*} [DecidableEq α] {f : α → α} (hf : Function.Involutive f)
    (F : Finset (Sym2 α)) (e : Sym2 α) : e ∈ F.image (Sym2.map f) ↔ Sym2.map f e ∈ F := by sorry
