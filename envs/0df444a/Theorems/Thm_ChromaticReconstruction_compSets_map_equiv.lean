-- Prove2me | Theorems.Thm_ChromaticReconstruction_compSets_map_equiv
-- name    : ChromaticReconstruction.compSets_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:27:48.659745+00:00
-- url     : https://prove2.me/theorems/0907970a-8ff2-4414-ae5a-44854860db9c
-- title:
--   Chromatic Reconstruction: comp Sets map equiv
-- statement:
--   Components are transported by a bijection that maps the edge sets onto each other.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L126-L157
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L126-L157

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]

theorem ChromaticReconstruction.compSets_map_equiv (e : V ≃ W) (A : Set (Sym2 V)) :
    compSets (Sym2.map e '' A) = (compSets A).image (Finset.map e.toEmbedding) := by sorry
