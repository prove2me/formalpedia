-- Prove2me | Theorems.Thm_ChromaticReconstruction_three_le_degree_PL_one
-- name    : ChromaticReconstruction.three_le_degree_PL_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:31.128577+00:00
-- url     : https://prove2.me/theorems/5abdbf8f-f344-4f64-97b2-48dd635e32cb
-- title:
--   Chromatic Reconstruction: three le degree PL one
-- statement:
--   The Chromatic Reconstruction construction uses the three le degree PL one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L118-L132
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/TauBound.lean#L118-L132

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.three_le_degree_PL_one {n : ℕ} (hn : 3 ≤ n) : 3 ≤ (PL n 1).degree (vx n 1) := by sorry
