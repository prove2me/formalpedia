-- Prove2me | Theorems.Thm_ChromaticReconstruction_pderiv_typeMonomial
-- name    : ChromaticReconstruction.pderiv_typeMonomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:33:43.489675+00:00
-- url     : https://prove2.me/theorems/5f1986e2-a656-47c3-b278-ce3d76ca35e5
-- title:
--   Chromatic Reconstruction: pderiv type Monomial
-- statement:
--   The Chromatic Reconstruction construction uses the pderiv type Monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L68-L79
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L68-L79

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.pderiv_typeMonomial (A : Set (Sym2 V)) (r : ℕ) :
    pderiv r (typeMonomial A) = ∑ C0 ∈ compSets A,
      if C0.card = r then ∏ C ∈ (compSets A).erase C0, (X C.card : MvPolynomial ℕ ℚ) else 0 := by sorry
