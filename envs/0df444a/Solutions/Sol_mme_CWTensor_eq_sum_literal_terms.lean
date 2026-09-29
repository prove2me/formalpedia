-- Prove2me | solution 1 for mme_CWTensor_eq_sum_literal_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:46:53.733756+00:00
-- url     : https://prove2.me/submissions/bc553815-e021-4f25-89c2-9e7dee3b2ad0

import Definitions.Def_mme_CW_fourth_literal_support_words
import Mathlib.Tactic

open MME BigOperators

universe u

namespace MME.StothersFourth

set_option autoImplicit false

end MME.StothersFourth

open MME.StothersFourth

/-- The defining CW tensor is exactly the sum of its `3q+3` enumerated
literal monomials. -/
theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q =
      ∑ t : CWLiteralTerm q, cwLiteralTermMonomial K q t := by
  have hM (i : Fin q) :
      (⟨i.val + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  have hT :
      (⟨q + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + q, by omega⟩ := by
    apply Fin.ext
    change q + 1 = 1 + q
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  unfold CWTensor cwLiteralTermMonomial
  simp [cwLiteralTermTriple, Fin.sum_univ_succ,
    cwZeroIndex, cwMiddleIndex, cwTopIndex, hM, hT]
  abel
