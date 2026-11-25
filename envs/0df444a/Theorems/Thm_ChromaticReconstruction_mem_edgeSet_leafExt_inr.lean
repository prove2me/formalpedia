-- Prove2me | Theorems.Thm_ChromaticReconstruction_mem_edgeSet_leafExt_inr
-- name    : ChromaticReconstruction.mem_edgeSet_leafExt_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:13:03.404565+00:00
-- url     : https://prove2.me/theorems/27f85fed-a130-4eb8-99f8-ddf9100febae
-- title:
--   Chromatic Reconstruction: mem edge Set leaf Ext inr
-- statement:
--   The Chromatic Reconstruction construction uses the mem edge Set leaf Ext inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L158-L163
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L158-L163

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

theorem ChromaticReconstruction.mem_edgeSet_leafExt_inr {l : Σ i, Fin (m i)} {w : K ⊕ Σ i, Fin (m i)}
    (h : s(.inr l, w) ∈ (leafExt S m).edgeSet) : w = .inl l.1 := by sorry
