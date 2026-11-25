-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_compType
-- name    : ChromaticReconstruction.sum_compType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:08:58.668233+00:00
-- url     : https://prove2.me/theorems/ffd1009f-96b2-4400-bb66-2ca8754c8243
-- title:
--   Chromatic Reconstruction: sum comp Type
-- statement:
--   The Chromatic Reconstruction construction uses the sum comp Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L83-L85
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L83-L85

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.sum_compType (A : Set (Sym2 V)) : (compType A).sum = Fintype.card V := by sorry
