-- Prove2me | Theorems.Thm_ChromaticReconstruction_prod_compSets_split
-- name    : ChromaticReconstruction.prod_compSets_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:07:03.389992+00:00
-- url     : https://prove2.me/theorems/9f31f19b-cb46-4191-9b85-b5a03e3bb6a9
-- title:
--   Chromatic Reconstruction: prod comp Sets split
-- statement:
--   Splitting off the component containing `v` in a product over components.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L56-L65
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L56-L65

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.prod_compSets_split {M : Type*} [CommMonoid M] (A : Set (Sym2 V)) (v : V)
    (f g : Finset V → M) :
    ∏ C ∈ compSets A, (if v ∈ C then g C else f C) =
      g (compOf A v) * ∏ C ∈ (compSets A).erase (compOf A v), f C := by sorry
