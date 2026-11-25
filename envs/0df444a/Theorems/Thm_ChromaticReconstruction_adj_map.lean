-- Prove2me | Theorems.Thm_ChromaticReconstruction_adj_map
-- name    : ChromaticReconstruction.adj_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:42:42.3318+00:00
-- url     : https://prove2.me/theorems/f3cd3cd5-f2ef-435a-8cbb-f23bbd62b0d2
-- title:
--   Chromatic Reconstruction: adj map
-- statement:
--   The Chromatic Reconstruction construction uses the adj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L355-L387
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L355-L387

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}

theorem ChromaticReconstruction.adj_map (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (hW : wts w = wts w') (hE : edgeTypes S w = edgeTypes S' w') (φ : K ≃ K')
    (hkey : ∀ x, keyOf S' w' (φ x) = keyOf S w x) {x y : K} (hxy : S.Adj x y) :
    S'.Adj (φ x) (φ y) := by sorry
