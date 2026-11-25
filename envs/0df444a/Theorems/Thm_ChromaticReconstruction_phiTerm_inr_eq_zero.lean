-- Prove2me | Theorems.Thm_ChromaticReconstruction_phiTerm_inr_eq_zero
-- name    : ChromaticReconstruction.phiTerm_inr_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:29:24.604841+00:00
-- url     : https://prove2.me/theorems/8d35d115-f998-440b-a59a-0a4f03a84f7e
-- title:
--   Chromatic Reconstruction: phi Term inr eq zero
-- statement:
--   The Chromatic Reconstruction construction uses the phi Term inr eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L287-L342
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L287-L342

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.phiTerm_inr_eq_zero {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) (l0 : Σ i, Fin (m i))
    (hnot : A ∉ S.edgeFinset.powerset.image (extEdges m l0)) : phiTerm A (.inr l0) = 0 := by sorry
