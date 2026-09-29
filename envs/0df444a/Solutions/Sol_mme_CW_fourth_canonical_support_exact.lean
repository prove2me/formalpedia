-- Prove2me | solution 1 for mme_CW_fourth_canonical_support_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:06:33.238564+00:00
-- url     : https://prove2.me/submissions/265d7121-e56f-4959-b5dc-d1a032aec255

import Theorems.Thm_mme_CW_fourth_support_pattern_surjective
import Theorems.Thm_mme_CW_canonical_four_literal_address_eq_support_pattern
import Theorems.Thm_mme_CW_fourth_block_nonzero_of_literal_terms
import Theorems.Thm_mme_CW_fourth_block_zero_of_grade_sum_ne_eight

open BigOperators

universe u

set_option autoImplicit false

/-- Exact support of the canonical fourth-power grading, uniformly for every
positive CW parameter represented by a chosen middle coordinate. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) (i : Fin q) :
    ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8 := by
  intro sigma
  constructor
  · intro hzero hsum
    obtain ⟨r, hr⟩ := mme_CW_fourth_support_pattern_surjective sigma hsum
    let w₁ := MME.StothersFourth.cwCanonicalSupportTerm q i (r 0)
    let w₂ := MME.StothersFourth.cwCanonicalSupportTerm q i (r 1)
    let w₃ := MME.StothersFourth.cwCanonicalSupportTerm q i (r 2)
    let w₄ := MME.StothersFourth.cwCanonicalSupportTerm q i (r 3)
    have hselected : ∀ s,
        MME.StothersFourth.cwFourthPairGrade q
          (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
            w₁ w₂ w₃ w₄ s) = sigma s := by
      intro s
      apply Fin.ext
      change (MME.StothersFourth.cwCanonicalFourLiteralAddress q i r s).val =
        (sigma s).val
      rw [mme_CW_canonical_four_literal_address_eq_support_pattern]
      exact hr s
    exact mme_CW_fourth_block_nonzero_of_literal_terms
      q sigma w₁ w₂ w₃ w₄ hselected hzero
  · intro hsum
    exact mme_CW_fourth_block_zero_of_grade_sum_ne_eight q sigma hsum
