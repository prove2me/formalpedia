-- Prove2me | Theorems.Thm_ChromaticReconstruction_typeMonomial_eq_monomial
-- name    : ChromaticReconstruction.typeMonomial_eq_monomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T12:08:58.75308+00:00
-- url     : https://prove2.me/theorems/27e2ee90-649e-4a08-8de4-f096e829f6d8
-- title:
--   Chromatic Reconstruction: type Monomial eq monomial
-- statement:
--   The Chromatic Reconstruction construction uses the type Monomial eq monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L75-L78
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CompStructure.lean#L75-L78

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.typeMonomial_eq_monomial (A : Set (Sym2 V)) :
    typeMonomial A = monomial (Multiset.toFinsupp (compType A)) 1 := by sorry
