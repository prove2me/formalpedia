-- Prove2me | Theorems.Thm_ChromaticReconstruction_exists_weighted_iso
-- name    : ChromaticReconstruction.exists_weighted_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:45:13.334453+00:00
-- url     : https://prove2.me/theorems/3ac5dba9-049a-4ad9-972c-20509db0240b
-- title:
--   Chromatic Reconstruction: exists weighted iso
-- statement:
--   **Weighted reconstruction.** Two weighted trees with the same weight multiset and the same
--   multiset of edge types are isomorphic as weighted trees, provided the first one is
--   multiplicity-isolated.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L392-L415
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L392-L415

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}

theorem ChromaticReconstruction.exists_weighted_iso (hS : S.IsTree) (hS' : S'.IsTree) (hW : wts w = wts w')
    (hE : edgeTypes S w = edgeTypes S' w') (hMI : MIso S w) :
    ∃ φ : S ≃g S', ∀ x, w' (φ x) = w x := by sorry
