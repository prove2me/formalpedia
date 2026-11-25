-- Prove2me | Theorems.Thm_ChromaticReconstruction_card_compSets_add_card_of_isTree
-- name    : ChromaticReconstruction.card_compSets_add_card_of_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:26:25.532415+00:00
-- url     : https://prove2.me/theorems/2bc24e87-64a5-47e0-b30b-58b7f3f98ed8
-- title:
--   Chromatic Reconstruction: card comp Sets add card of is Tree
-- statement:
--   **Forest formula.** For a tree `S` and `F ⊆ E(S)`, `|Comp(F)| + |F| = |V|`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L137-L146
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L137-L146

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.card_compSets_add_card_of_isTree {S : SimpleGraph V} (hS : S.IsTree)
    {F : Finset (Sym2 V)} (hF : F ⊆ S.edgeFinset) :
    (compSets (F : Set (Sym2 V))).card + F.card = Fintype.card V := by sorry
