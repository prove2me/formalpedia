-- Prove2me | Theorems.Thm_ChromaticReconstruction_degree_one_of_repeated
-- name    : ChromaticReconstruction.degree_one_of_repeated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:27:45.915406+00:00
-- url     : https://prove2.me/theorems/22eb71e8-531b-453a-9841-9b5f46c579d8
-- title:
--   Chromatic Reconstruction: degree one of repeated
-- statement:
--   The Chromatic Reconstruction construction uses the degree one of repeated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L218-L221
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L218-L221

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}

theorem ChromaticReconstruction.degree_one_of_repeated {w : K → ℕ} (hMI : MIso S w) {x : K}
    (h : Multiset.count (w x) (wts w) ≠ 1) : S.degree x = 1 := by sorry
