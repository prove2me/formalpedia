-- Prove2me | Theorems.Thm_ChromaticReconstruction_extEdges_subset
-- name    : ChromaticReconstruction.extEdges_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:19:22.034795+00:00
-- url     : https://prove2.me/theorems/11c954c6-288c-413e-88b9-9b1527bf4a61
-- title:
--   Chromatic Reconstruction: ext Edges subset
-- statement:
--   The Chromatic Reconstruction construction uses the ext Edges subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L193-L203
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L193-L203

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.extEdges_subset {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} (hF : F ⊆ S.edgeFinset) :
    extEdges m l0 F ⊆ (leafExt S m).edgeFinset := by sorry
