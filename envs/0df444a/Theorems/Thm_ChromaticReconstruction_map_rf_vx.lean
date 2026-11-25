-- Prove2me | Theorems.Thm_ChromaticReconstruction_map_rf_vx
-- name    : ChromaticReconstruction.map_rf_vx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:51:29.871808+00:00
-- url     : https://prove2.me/theorems/92609695-3a2d-4028-975e-7292c6aaa3ea
-- title:
--   Chromatic Reconstruction: map rf vx
-- statement:
--   The Chromatic Reconstruction construction uses the map rf vx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L43-L45
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L43-L45

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.map_rf_vx {s a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    Sym2.map (rf n c s) s(vx n a, vx n b) = s(vx n (rfv c s a), vx n (rfv c s b)) := by sorry
