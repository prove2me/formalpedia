-- Prove2me | solution 1 for mme_stothers_fourth_block_zero_of_grade_sum_ne_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:05:59.600933+00:00
-- url     : https://prove2.me/submissions/c115afa3-1756-4e75-9793-6d3225eacb15

import Theorems.Thm_mme_CW_fourth_block_zero_of_grade_sum_ne_eight

open BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 := by
  exact mme_CW_fourth_block_zero_of_grade_sum_ne_eight 6 sigma hsum
