-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_compType
-- name    : ChromaticReconstruction.card_compType
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:22:21.372827+00:00
-- url     : https://prove2.me/theorems/13496538-3270-4f43-bb7b-3a7135d9b7ee
-- title:
--   Chromatic Reconstruction: card comp Type
-- statement:
--   The Chromatic Reconstruction construction uses the card comp Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L80-L81
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L80-L81

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.card_compType (A : Set (Sym2 V)) : Multiset.card (compType A) = (compSets A).card := by sorry
