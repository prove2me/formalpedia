-- Prove2me | Theorems.Thm_ChromaticReconstruction_extEdges_injective
-- name    : ChromaticReconstruction.extEdges_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:20:43.009079+00:00
-- url     : https://prove2.me/theorems/e247724d-40f6-43d7-8f54-b0d2db5cdb21
-- title:
--   Chromatic Reconstruction: ext Edges injective
-- statement:
--   The Chromatic Reconstruction construction uses the ext Edges injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L205-L211
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L205-L211

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.extEdges_injective (l0 : Σ i, Fin (m i)) : Function.Injective (extEdges m l0) := by sorry
