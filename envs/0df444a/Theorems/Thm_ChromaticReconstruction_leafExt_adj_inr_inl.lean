-- Prove2me | Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
-- name    : ChromaticReconstruction.leafExt_adj_inr_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:22:36.903484+00:00
-- url     : https://prove2.me/theorems/67dba371-a2f7-49c4-a945-d327090ed42a
-- title:
--   Chromatic Reconstruction: leaf Ext adj inr inl
-- statement:
--   The Chromatic Reconstruction construction uses the leaf Ext adj inr inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L41-L42
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L41-L42

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
omit [Fintype K]

theorem ChromaticReconstruction.leafExt_adj_inr_inl {i : K} {l : Σ i, Fin (m i)} :
    (leafExt S m).Adj (.inr l) (.inl i) ↔ l.1 = i := by sorry
