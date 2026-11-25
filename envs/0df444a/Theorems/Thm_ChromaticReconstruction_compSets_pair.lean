-- Prove2me | Theorems.Thm_ChromaticReconstruction_compSets_pair
-- name    : ChromaticReconstruction.compSets_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:30:18.458208+00:00
-- url     : https://prove2.me/theorems/ff95549d-ddbc-4368-83d3-f657671e5571
-- title:
--   Chromatic Reconstruction: comp Sets pair
-- statement:
--   Components of a single edge.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L136-L171
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L136-L171

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.compSets_pair {u v : V} :
    compSets ({s(u, v)} : Set (Sym2 V)) =
      insert {u, v} ((univ \ {u, v}).image fun w => ({w} : Finset V)) := by sorry
