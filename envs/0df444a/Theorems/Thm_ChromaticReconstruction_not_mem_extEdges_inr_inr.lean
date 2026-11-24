-- Prove2me | Theorems.Thm_ChromaticReconstruction_not_mem_extEdges_inr_inr
-- name    : ChromaticReconstruction.not_mem_extEdges_inr_inr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:31:40.339124+00:00
-- url     : https://prove2.me/theorems/62519b05-d1fd-4c09-a1bd-d249cb40ae5e
-- title:
--   Chromatic Reconstruction: not mem ext Edges inr inr
-- statement:
--   The Chromatic Reconstruction construction uses the not mem ext Edges inr inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L79-L86
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L79-L86

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.not_mem_extEdges_inr_inr {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)}
    {l l' : Σ i, Fin (m i)} : s(.inr l, .inr l') ∉ extEdges m l0 F := by sorry
