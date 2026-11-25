-- Prove2me | Theorems.Thm_ChromaticReconstruction_phiTerm_extEdges
-- name    : ChromaticReconstruction.phiTerm_extEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:24:01.114366+00:00
-- url     : https://prove2.me/theorems/89cc6ea3-2f05-49ef-b8f0-b05d3ca73c4d
-- title:
--   Chromatic Reconstruction: phi Term ext Edges
-- statement:
--   The Chromatic Reconstruction construction uses the phi Term ext Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L263-L285
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L263-L285

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.phiTerm_extEdges (l0 : Σ i, Fin (m i)) (F : Finset (Sym2 K)) :
    phiTerm (extEdges m l0 F) (.inr l0) =
      (-1) ^ ((∑ i, m i) - 1 + F.card) * killP1 (∏ C ∈ compSets (F : Set (Sym2 K)),
        X ((∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0)) := by sorry
