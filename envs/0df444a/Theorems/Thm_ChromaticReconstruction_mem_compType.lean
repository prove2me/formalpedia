-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_compType
-- name    : ChromaticReconstruction.mem_compType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:25:46.272729+00:00
-- url     : https://prove2.me/theorems/fa53c97b-1a4a-447e-a9a9-1ab96a117148
-- title:
--   Chromatic Reconstruction: mem comp Type
-- statement:
--   The Chromatic Reconstruction construction uses the mem comp Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L87-L89
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L87-L89

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.mem_compType {A : Set (Sym2 V)} {r : ℕ} :
    r ∈ compType A ↔ ∃ C ∈ compSets A, C.card = r := by sorry
