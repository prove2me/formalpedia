-- Prove2me | Theorems.Thm_ChromaticReconstruction_pe_inj
-- name    : ChromaticReconstruction.pe_inj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:47:47.525714+00:00
-- url     : https://prove2.me/theorems/5dc5fd2d-d770-42fc-a14c-364dc4f10e39
-- title:
--   Chromatic Reconstruction: pe inj
-- statement:
--   The Chromatic Reconstruction construction uses the pe inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L47-L49
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L47-L49

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.pe_inj {n i j : ℕ} (hi : i + 1 ≤ n) (hj : j + 1 ≤ n) : pe n i = pe n j ↔ i = j := by sorry
