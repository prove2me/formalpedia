-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inr
-- name    : ChromaticReconstruction.mem_extEdges_inl_inr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:26:23.664679+00:00
-- url     : https://prove2.me/theorems/ed290d5f-4811-4f24-9765-23b473152d41
-- title:
--   Chromatic Reconstruction: mem ext Edges inl inr
-- statement:
--   The Chromatic Reconstruction construction uses the mem ext Edges inl inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L58-L72
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L58-L72

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.mem_extEdges_inl_inr {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} {a : K}
    {l : Σ i, Fin (m i)} :
    s(.inl a, .inr l) ∈ extEdges m l0 F ↔ l.1 = a ∧ l ≠ l0 := by sorry
