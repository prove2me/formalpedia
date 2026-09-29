-- Prove2me | solution 1 for mme_CW_square_q6_five_grade_orbit_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:44:16.127807+00:00
-- url     : https://prove2.me/submissions/830f21be-dfd4-427f-8d80-8a506c4c2619

import Definitions.Def_mme_CW_square_canonical_grading
import Theorems.Thm_mme_CW_public_cyclic_orbit_product_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Mathlib.Tactic

open MME

universe u

private theorem cyclicSymmetrization_eq_publicKron
    {K : Type u} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X =
      TensorObj.kron X
        (TensorObj.kron (TensorObj.permObj cyclicPerm X)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

theorem solution
    {K : Type u} [Field K] :
    Nonempty (CWSquareFiveGradeCertificate K 6) := by
  rcases mme_CW_square_canonical_elementary_blocks (K := K) 6 with
    ⟨hsupport, h004, h040, h400,
      h013, h031, h103, h301, h130, h310,
      h022, h202, h220⟩
  have h112 := mme_CW_square_canonical_coupled112_restrict (K := K) 6
  have h211 := mme_CW_square_canonical_coupled211_restrict (K := K) 6
  have h121 := mme_CW_square_canonical_coupled121_restrict (K := K) 6
  have hproduct :=
    mme_CW_public_cyclic_orbit_product_restrict (K := K) 6 h112 h211 h121
  have hcyclic :
      TensorObj.Restrict
        (cyclicSymmetrization (coupledObj K 6))
        (TensorObj.kron
          ((cwSquareCanonicalGrading K 6).blockSubtensor
            (cwSquareBlockType 1 1 2))
          (TensorObj.kron
            ((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 2 1 1))
            ((cwSquareCanonicalGrading K 6).blockSubtensor
              (cwSquareBlockType 1 2 1)))) := by
    rw [cyclicSymmetrization_eq_publicKron]
    exact hproduct
  exact ⟨{
    grading := cwSquareCanonicalGrading K 6
    support := hsupport
    scalar004 := h004
    scalar040 := h040
    scalar400 := h400
    rect013 := h013
    rect031 := h031
    rect103 := h103
    rect301 := h301
    rect130 := h130
    rect310 := h310
    central022 := h022
    central202 := h202
    central220 := h220
    coupled112 := h112
    coupledCyclic := hcyclic
  }⟩
