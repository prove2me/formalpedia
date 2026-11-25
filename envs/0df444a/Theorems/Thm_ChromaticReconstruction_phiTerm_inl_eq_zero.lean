-- Prove2me | Theorems.Thm_ChromaticReconstruction_phiTerm_inl_eq_zero
-- name    : ChromaticReconstruction.phiTerm_inl_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:19:38.86691+00:00
-- url     : https://prove2.me/theorems/41100538-4c85-4f03-ba0f-2a7d94fbd596
-- title:
--   Chromatic Reconstruction: phi Term inl eq zero
-- statement:
--   The Chromatic Reconstruction construction uses the phi Term inl eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L181-L191
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L181-L191

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.phiTerm_inl_eq_zero (hm : ∀ i, 1 ≤ m i) {A : Finset (Sym2 (K ⊕ Σ i, Fin (m i)))}
    (hA : A ⊆ (leafExt S m).edgeFinset) (i : K) : phiTerm A (.inl i) = 0 := by sorry
