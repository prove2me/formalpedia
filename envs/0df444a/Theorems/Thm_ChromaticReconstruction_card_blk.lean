-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_blk
-- name    : ChromaticReconstruction.card_blk
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:23:14.368894+00:00
-- url     : https://prove2.me/theorems/a1b1296f-7a06-4577-ae85-6393d884052b
-- title:
--   Chromatic Reconstruction: card blk
-- statement:
--   The Chromatic Reconstruction construction uses the card blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L237-L261
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L237-L261

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.card_blk (l0 : Σ i, Fin (m i)) (C : Finset K) :
    (blk m l0 C).card = (∑ i ∈ C, (m i + 1)) - if l0.1 ∈ C then 1 else 0 := by sorry
