-- Prove2me | Theorems.Thm_ChromaticReconstruction_rf_vx
-- name    : ChromaticReconstruction.rf_vx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:56:31.341176+00:00
-- url     : https://prove2.me/theorems/caf315e9-df8f-4a3f-aa84-b6d3e951f2e0
-- title:
--   Chromatic Reconstruction: rf vx
-- statement:
--   The Chromatic Reconstruction construction uses the rf vx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L35-L36
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L35-L36

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.rf_vx {s x : ℕ} (hx : x ≤ n) : rf n c s (vx n x) = vx n (rfv c s x) := by sorry
