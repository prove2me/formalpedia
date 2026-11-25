-- Prove2me | Theorems.Thm_ChromaticReconstruction_PL_walk_zero
-- name    : ChromaticReconstruction.PL_walk_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:02:47.550862+00:00
-- url     : https://prove2.me/theorems/98f01ded-b434-4f7a-8faf-6aac2e8c211f
-- title:
--   Chromatic Reconstruction: PL walk zero
-- statement:
--   A walk along the path from `0` to `i`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L19-L25
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L19-L25

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.PL_walk_zero {n c : ℕ} : ∀ i, i < n → ∃ w : (PL n c).Walk (vx n 0) (vx n i), w.length = i
  := by sorry
