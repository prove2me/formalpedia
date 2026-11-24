-- Prove2me | Theorems.Thm_ChromaticReconstruction_adj_map_of_repeated
-- name    : ChromaticReconstruction.adj_map_of_repeated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:41:13.656384+00:00
-- url     : https://prove2.me/theorems/41932da8-e88c-4ee0-9133-8309d62a4308
-- title:
--   Chromatic Reconstruction: adj map of repeated
-- statement:
--   The Chromatic Reconstruction construction uses the adj map of repeated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L336-L353
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L336-L353

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}

theorem ChromaticReconstruction.adj_map_of_repeated (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (hW : wts w = wts w') (φ : K ≃ K') (hkey : ∀ x, keyOf S' w' (φ x) = keyOf S w x) {x y : K}
    (hxy : S.Adj x y) (hx : Multiset.count (w x) (wts w) ≠ 1) : S'.Adj (φ x) (φ y) := by sorry
