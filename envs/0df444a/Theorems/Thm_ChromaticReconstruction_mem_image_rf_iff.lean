-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_image_rf_iff
-- name    : ChromaticReconstruction.mem_image_rf_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:58:07.417682+00:00
-- url     : https://prove2.me/theorems/b3f3e508-a04f-409c-9fee-08ced32e2205
-- title:
--   Chromatic Reconstruction: mem image rf iff
-- statement:
--   The Chromatic Reconstruction construction uses the mem image rf iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L137-L140
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L137-L140

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}

theorem ChromaticReconstruction.mem_image_rf_iff {s a b : ℕ} (hs : c + s ≤ n) (hs' : s ≤ c + 1) (ha : a ≤ n) (hb : b ≤ n) :
    s(vx n a, vx n b) ∈ F.image (Sym2.map (rf n c s)) ↔
      s(vx n (rfv c s a), vx n (rfv c s b)) ∈ F := by sorry
