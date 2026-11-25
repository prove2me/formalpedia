-- Prove2me | Theorems.Thm_ChromaticReconstruction_unique_of_adj_leaf
-- name    : ChromaticReconstruction.unique_of_adj_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:47:37.1866+00:00
-- url     : https://prove2.me/theorems/4ee7c650-efd6-4d12-86ea-0d167a9ed140
-- title:
--   Chromatic Reconstruction: unique of adj leaf
-- statement:
--   The Chromatic Reconstruction construction uses the unique of adj leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L223-L228
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L223-L228

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}

theorem ChromaticReconstruction.unique_of_adj_leaf {w : K → ℕ} (hS : S.Connected) (hk : 3 ≤ Fintype.card K)
    (hMI : MIso S w) {x y : K} (hx : S.degree x = 1) (hxy : S.Adj x y) :
    Multiset.count (w y) (wts w) = 1 := by sorry
