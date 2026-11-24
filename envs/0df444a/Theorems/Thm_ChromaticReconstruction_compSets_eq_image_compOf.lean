-- Prove2me | Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf
-- name    : ChromaticReconstruction.compSets_eq_image_compOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:23:32.28594+00:00
-- url     : https://prove2.me/theorems/e31645df-a66c-408d-b981-e0506a924553
-- title:
--   Chromatic Reconstruction: comp Sets eq image comp Of
-- statement:
--   The Chromatic Reconstruction construction uses the comp Sets eq image comp Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L19-L19
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Forest.lean#L19-L19

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.compSets_eq_image_compOf (A : Set (Sym2 V)) : compSets A = univ.image (compOf A) := by sorry
