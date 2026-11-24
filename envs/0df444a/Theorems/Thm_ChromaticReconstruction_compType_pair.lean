-- Prove2me | Theorems.Thm_ChromaticReconstruction_compType_pair
-- name    : ChromaticReconstruction.compType_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:10:39.95156+00:00
-- url     : https://prove2.me/theorems/390fc46e-a5f3-4846-aedd-7bd513030e7a
-- title:
--   Chromatic Reconstruction: comp Type pair
-- statement:
--   The Chromatic Reconstruction construction uses the comp Type pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L173-L188
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L173-L188

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.compType_pair {u v : V} (huv : u ≠ v) :
    compType ({s(u, v)} : Set (Sym2 V)) = 2 ::ₘ Multiset.replicate (Fintype.card V - 2) 1 := by sorry
