-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_extEdges
-- name    : ChromaticReconstruction.card_extEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:21:47.91778+00:00
-- url     : https://prove2.me/theorems/7ad5abb6-1eee-4b9a-8207-7dfc5e11e3cb
-- title:
--   Chromatic Reconstruction: card ext Edges
-- statement:
--   The Chromatic Reconstruction construction uses the card ext Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L213-L229
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/LeafExtMaster.lean#L213-L229

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}

theorem ChromaticReconstruction.card_extEdges (l0 : Σ i, Fin (m i)) (F : Finset (Sym2 K)) :
    (extEdges m l0 F).card = (∑ i, m i) - 1 + F.card := by sorry
