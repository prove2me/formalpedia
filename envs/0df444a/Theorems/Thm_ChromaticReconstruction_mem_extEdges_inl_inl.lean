-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inl
-- name    : ChromaticReconstruction.mem_extEdges_inl_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:26:21.501542+00:00
-- url     : https://prove2.me/theorems/817e221e-3051-4327-8821-f4e14e6ee75c
-- title:
--   Chromatic Reconstruction: mem ext Edges inl inl
-- statement:
--   The Chromatic Reconstruction construction uses the mem ext Edges inl inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L47-L56
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L47-L56

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.mem_extEdges_inl_inl {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} {a b : K} :
    s(.inl a, .inl b) ∈ extEdges m l0 F ↔ s(a, b) ∈ F := by sorry
