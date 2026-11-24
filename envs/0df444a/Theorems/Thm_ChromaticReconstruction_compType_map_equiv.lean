-- Prove2me | Theorems.Thm_ChromaticReconstruction_compType_map_equiv
-- name    : ChromaticReconstruction.compType_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:27:54.818988+00:00
-- url     : https://prove2.me/theorems/e0b03d63-53b5-42f2-84b9-88b7acd0417f
-- title:
--   Chromatic Reconstruction: comp Type map equiv
-- statement:
--   The Chromatic Reconstruction construction uses the comp Type map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L167-L173
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L167-L173

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]

theorem ChromaticReconstruction.compType_map_equiv (e : V ≃ W) (A : Set (Sym2 V)) :
    compType (Sym2.map e '' A) = compType A := by sorry
