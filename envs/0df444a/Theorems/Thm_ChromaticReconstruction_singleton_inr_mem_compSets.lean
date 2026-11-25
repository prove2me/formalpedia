-- Prove2me | Theorems.Thm_ChromaticReconstruction_singleton_inr_mem_compSets
-- name    : ChromaticReconstruction.singleton_inr_mem_compSets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:32:16.681193+00:00
-- url     : https://prove2.me/theorems/0311ff07-a4d3-42d1-b54a-ab52bf91650c
-- title:
--   Chromatic Reconstruction: singleton inr mem comp Sets
-- statement:
--   A leaf whose edge is not selected is isolated.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L170-L179
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L170-L179

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.singleton_inr_mem_compSets {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) {l : Σ i, Fin (m i)} (hl : leafEdge m l ∉ A) :
    {.inr l} ∈ compSets (A : Set (Sym2 (K ⊕ Σ i, Fin (m i)))) := by sorry
