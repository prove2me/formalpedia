-- Prove2me | Theorems.Thm_ChromaticReconstruction_vx_inj
-- name    : ChromaticReconstruction.vx_inj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:27:21.308058+00:00
-- url     : https://prove2.me/theorems/41cf42e9-556b-41ed-8a59-2c9516e5d465
-- title:
--   Chromatic Reconstruction: vx inj
-- statement:
--   The Chromatic Reconstruction construction uses the vx inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L25-L26
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L25-L26

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.vx_inj {n x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) : vx n x = vx n y ↔ x = y := by sorry
