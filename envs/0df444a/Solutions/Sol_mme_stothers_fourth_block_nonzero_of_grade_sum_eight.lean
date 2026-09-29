-- Prove2me | solution 1 for mme_stothers_fourth_block_nonzero_of_grade_sum_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:05:59.599119+00:00
-- url     : https://prove2.me/submissions/682dca30-3f09-411d-a721-5c8a326c1fd9

import Theorems.Thm_mme_CW_fourth_support_pattern_surjective
import Theorems.Thm_mme_CW_canonical_four_literal_address_eq_support_pattern
import Theorems.Thm_mme_CW_fourth_block_nonzero_of_literal_terms

open BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) = 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 := by
  obtain ⟨r, hr⟩ := mme_CW_fourth_support_pattern_surjective sigma hsum
  let i : Fin 6 := 0
  let w₁ := MME.StothersFourth.cwCanonicalSupportTerm 6 i (r 0)
  let w₂ := MME.StothersFourth.cwCanonicalSupportTerm 6 i (r 1)
  let w₃ := MME.StothersFourth.cwCanonicalSupportTerm 6 i (r 2)
  let w₄ := MME.StothersFourth.cwCanonicalSupportTerm 6 i (r 3)
  apply mme_CW_fourth_block_nonzero_of_literal_terms
    6 sigma w₁ w₂ w₃ w₄
  intro s
  apply Fin.ext
  change (MME.StothersFourth.cwCanonicalFourLiteralAddress 6 i r s).val =
    (sigma s).val
  rw [mme_CW_canonical_four_literal_address_eq_support_pattern]
  exact hr s
