-- Prove2me | Theorems.Thm_ChromaticReconstruction_typeMonomial_map_equiv
-- name    : ChromaticReconstruction.typeMonomial_map_equiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:57:45.392013+00:00
-- url     : https://prove2.me/theorems/c211143a-b031-4d56-b20c-8dce8b51e38a
-- title:
--   Chromatic Reconstruction: type Monomial map equiv
-- statement:
--   The Chromatic Reconstruction construction uses the type Monomial map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L159-L165
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L159-L165

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]

theorem ChromaticReconstruction.typeMonomial_map_equiv (e : V ≃ W) (A : Set (Sym2 V)) :
    typeMonomial (Sym2.map e '' A) = typeMonomial A := by sorry
