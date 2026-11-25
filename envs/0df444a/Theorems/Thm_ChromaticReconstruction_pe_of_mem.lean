-- Prove2me | Theorems.Thm_ChromaticReconstruction_pe_of_mem
-- name    : ChromaticReconstruction.pe_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:17:32.048795+00:00
-- url     : https://prove2.me/theorems/d91fcbff-4c0c-4e19-82b4-03eb1c243615
-- title:
--   Chromatic Reconstruction: pe of mem
-- statement:
--   The Chromatic Reconstruction construction uses the pe of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L240-L245
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L240-L245

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

theorem ChromaticReconstruction.pe_of_mem {e : Sym2 (Fin (n + 1))} (hpn : p < n) (hF : F ⊆ (PL n p).edgeFinset)
    (he : e ∈ F) (hne : e ≠ lf n p) : ∃ i, i + 1 < n ∧ e = pe n i := by sorry
