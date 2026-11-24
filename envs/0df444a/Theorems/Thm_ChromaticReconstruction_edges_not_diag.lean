-- Prove2me | Theorems.Thm_ChromaticReconstruction_edges_not_diag
-- name    : ChromaticReconstruction.edges_not_diag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:34:14.380344+00:00
-- url     : https://prove2.me/theorems/c2caf62d-5249-4a2b-82f4-01f432319ea6
-- title:
--   Chromatic Reconstruction: edges not diag
-- statement:
--   The Chromatic Reconstruction construction uses the edges not diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/ChromCoeff.lean#L17-L22
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/ChromCoeff.lean#L17-L22

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.edges_not_diag (G : SimpleGraph V) {A : Finset (Sym2 V)} (hA : A ⊆ G.edgeFinset) :
    ∀ e ∈ A, ¬ e.IsDiag := by sorry
