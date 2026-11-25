-- Prove2me | Theorems.Thm_ChromaticReconstruction_PL_not_iso
-- name    : ChromaticReconstruction.PL_not_iso
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:13:07.027684+00:00
-- url     : https://prove2.me/theorems/54851d4c-6eb1-43b0-b4fd-8000d6915a66
-- title:
--   Chromatic Reconstruction: PL not iso
-- statement:
--   The two trees `PL n (b-1)` and `PL n b` are not isomorphic.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L145-L155
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L145-L155

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.PL_not_iso {n b : ℕ} (hb : 1 ≤ b) (hn : 2 * b + 1 ≤ n) :
    IsEmpty (PL n (b - 1) ≃g PL n b) := by sorry
