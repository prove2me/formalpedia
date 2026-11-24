-- Prove2me | Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
-- name    : ChromaticReconstruction.leafExt_adj_inr_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:22:13.717671+00:00
-- url     : https://prove2.me/theorems/ed1757be-69d3-429a-a9ed-c21a923af604
-- title:
--   Chromatic Reconstruction: leaf Ext adj inr inr
-- statement:
--   The Chromatic Reconstruction construction uses the leaf Ext adj inr inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L44-L45
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L44-L45

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

theorem ChromaticReconstruction.leafExt_adj_inr_inr {l l' : Σ i, Fin (m i)} :
    ¬ (leafExt S m).Adj (.inr l) (.inr l') := by sorry
