-- Prove2me | Theorems.Thm_ChromaticReconstruction_compSets_extEdges
-- name    : ChromaticReconstruction.compSets_extEdges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:11:55.662324+00:00
-- url     : https://prove2.me/theorems/bec5eb44-bc21-4cd1-b99f-144684bc5a19
-- title:
--   Chromatic Reconstruction: comp Sets ext Edges
-- statement:
--   The components of `(V, L₀ ∪ F)`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L89-L155
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L89-L155

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.compSets_extEdges (l0 : Σ i, Fin (m i)) (F : Finset (Sym2 K)) :
    compSets (extEdges m l0 F : Set (Sym2 (K ⊕ Σ i, Fin (m i)))) =
      insert {.inr l0} ((compSets (F : Set (Sym2 K))).image (blk m l0)) := by sorry
