-- Prove2me | Theorems.Thm_ChromaticReconstruction_PL_adj_vx
-- name    : ChromaticReconstruction.PL_adj_vx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:23:55.393572+00:00
-- url     : https://prove2.me/theorems/7c8463ab-0cae-48c1-adfd-dea005b5aae4
-- title:
--   Chromatic Reconstruction: PL adj vx
-- statement:
--   The Chromatic Reconstruction construction uses the PL adj vx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L61-L65
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeaf.lean#L61-L65

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.PL_adj_vx {n c x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) :
    (PL n c).Adj (vx n x) (vx n y) ↔ (x + 1 = y ∧ y < n) ∨ (y + 1 = x ∧ x < n) ∨
      (x = c ∧ y = n ∧ c < n) ∨ (y = c ∧ x = n ∧ c < n) := by sorry
