-- Prove2me | Theorems.Thm_ChromaticReconstruction_layer_edges
-- name    : ChromaticReconstruction.layer_edges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:19:45.191212+00:00
-- url     : https://prove2.me/theorems/c6d21a85-853c-4aca-80a6-740aceb043ee
-- title:
--   Chromatic Reconstruction: layer edges
-- statement:
--   The Chromatic Reconstruction construction uses the layer edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L79-L97
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/RecoveryThm.lean#L79-L97

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)

theorem ChromaticReconstruction.layer_edges (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) (hk : 2 ≤ Fintype.card K) :
    homogeneousComponent (Fintype.card K - 1) (phi (leafExt S m)) =
      (-1) ^ ((∑ i, m i) - 1 + 1) *
        ((edgeTypes S (fun i => m i + 1)).map (theta (weightMS m))).sum := by sorry
