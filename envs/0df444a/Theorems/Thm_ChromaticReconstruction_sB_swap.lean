-- Prove2me | Theorems.Thm_ChromaticReconstruction_sB_swap
-- name    : ChromaticReconstruction.sB_swap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:07:54.157247+00:00
-- url     : https://prove2.me/theorems/bd9c9807-fd94-4193-a41f-f8b8767637a3
-- title:
--   Chromatic Reconstruction: s B swap
-- statement:
--   The first common break is preserved by the reflection.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L177-L223
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L177-L223

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

theorem ChromaticReconstruction.sB_swap (hn : 2 * c + 3 ≤ n)
    (hF : F ⊆ (PL n p).edgeFinset) (hb : HasBrk n c F) :
    sB n c (F.image (Sym2.map (rf n c (sB n c F)))) = sB n c F := by sorry
