-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_compSets_le_union
-- name    : ChromaticReconstruction.card_compSets_le_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:08:09.628614+00:00
-- url     : https://prove2.me/theorems/31cacd9d-189b-440e-8759-850bb5affccd
-- title:
--   Chromatic Reconstruction: card comp Sets le union
-- statement:
--   The Chromatic Reconstruction construction uses the card comp Sets le union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L126-L134
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L126-L134

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.card_compSets_le_union (A D : Finset (Sym2 V)) :
    (compSets (A : Set (Sym2 V))).card ≤ (compSets ((A ∪ D : Finset _) : Set (Sym2 V))).card +
      D.card := by sorry
