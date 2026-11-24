-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL
-- name    : ChromaticReconstruction.mem_edgeSet_PL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:24:04.898613+00:00
-- url     : https://prove2.me/theorems/4eea27e7-0668-4513-be1c-941b5dfa730b
-- title:
--   Chromatic Reconstruction: mem edge Set PL
-- statement:
--   The Chromatic Reconstruction construction uses the mem edge Set PL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L67-L85
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L67-L85

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.mem_edgeSet_PL {n c : ℕ} (hc : c < n) (e : Sym2 (Fin (n + 1))) :
    e ∈ (PL n c).edgeSet ↔ (∃ i, i + 1 < n ∧ e = pe n i) ∨ e = lf n c := by sorry
