-- Prove2me | Theorems.Thm_ChromaticReconstruction_swap_subset
-- name    : ChromaticReconstruction.swap_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:07:30.08125+00:00
-- url     : https://prove2.me/theorems/0160c227-314d-4fec-85e9-8e2fee9ab71b
-- title:
--   Chromatic Reconstruction: swap subset
-- statement:
--   The reflected edge set lies in the other tree.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L149-L174
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L149-L174

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

theorem ChromaticReconstruction.swap_subset (hn : 2 * c + 3 ≤ n) (hp : p = c ∨ p = c + 1)
    (hF : F ⊆ (PL n p).edgeFinset) (hb : HasBrk n c F) :
    F.image (Sym2.map (rf n c (sB n c F))) ⊆ (PL n (2 * c + 1 - p)).edgeFinset := by sorry
