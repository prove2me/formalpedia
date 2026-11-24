-- Prove2me | Theorems.Thm_ChromaticReconstruction_leafEdge_mem_edgeSet
-- name    : ChromaticReconstruction.leafEdge_mem_edgeSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:17:59.108049+00:00
-- url     : https://prove2.me/theorems/712f410d-b2a9-4f16-8ef1-3c9a3befef2d
-- title:
--   Chromatic Reconstruction: leaf Edge mem edge Set
-- statement:
--   The Chromatic Reconstruction construction uses the leaf Edge mem edge Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L166-L167
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L166-L167

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
omit [Fintype K]

theorem ChromaticReconstruction.leafEdge_mem_edgeSet (l : Σ i, Fin (m i)) : leafEdge m l ∈ (leafExt S m).edgeSet := by sorry
