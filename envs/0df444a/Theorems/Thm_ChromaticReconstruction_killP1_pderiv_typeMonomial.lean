-- Prove2me | Theorems.Thm_ChromaticReconstruction_killP1_pderiv_typeMonomial
-- name    : ChromaticReconstruction.killP1_pderiv_typeMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:59:15.001821+00:00
-- url     : https://prove2.me/theorems/2ce0ad50-8cc7-4237-913e-92c53beb8946
-- title:
--   Chromatic Reconstruction: kill P1 pderiv type Monomial
-- statement:
--   The Chromatic Reconstruction construction uses the kill P1 pderiv type Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PhiFormula.lean#L67-L87
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PhiFormula.lean#L67-L87

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.killP1_pderiv_typeMonomial (A : Set (Sym2 V)) :
    killP1 (pderiv 1 (typeMonomial A)) =
      ∑ v, if {v} ∈ compSets A then killP1 (∏ D ∈ (compSets A).erase {v}, X D.card) else 0 := by sorry
