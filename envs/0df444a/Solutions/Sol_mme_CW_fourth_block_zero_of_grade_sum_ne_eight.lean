-- Prove2me | solution 1 for mme_CW_fourth_block_zero_of_grade_sum_ne_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:05:59.592318+00:00
-- url     : https://prove2.me/submissions/ad2f34f0-cd9b-4611-a838-4fc8672f5b5f

import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight

open MME BigOperators

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- Every unsupported block of the literal fourth CW power vanishes. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma = 0 := by
  let F := PiTensorProduct.map
      (fun s => (MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
        s (sigma s))
  change F (MME.StothersFourth.cwFourthObj K q).t = 0
  rw [mme_CW_fourth_tensor_eq_sum_literal_terms]
  let f₄ := fun t₄ : MME.StothersFourth.CWLiteralTerm q =>
    ∑ t₃ : MME.StothersFourth.CWLiteralTerm q,
    ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
    ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
      MME.interchange
        (MME.interchange
          (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
          (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
        (MME.interchange
          (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
          (MME.StothersFourth.cwLiteralTermMonomial K q t₄))
  calc
    _ = ∑ t₄ : MME.StothersFourth.CWLiteralTerm q, F (f₄ t₄) :=
      map_sum F f₄ Finset.univ
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t₄
      let f₃ := fun t₃ : MME.StothersFourth.CWLiteralTerm q =>
        ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
        ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
          MME.interchange
            (MME.interchange
              (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
              (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
            (MME.interchange
              (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
              (MME.StothersFourth.cwLiteralTermMonomial K q t₄))
      calc
        F (f₄ t₄) = ∑ t₃ : MME.StothersFourth.CWLiteralTerm q,
            F (f₃ t₃) := by
          dsimp only [f₄]
          exact map_sum F f₃ Finset.univ
        _ = 0 := by
          apply Fintype.sum_eq_zero
          intro t₃
          let f₂ := fun t₂ : MME.StothersFourth.CWLiteralTerm q =>
            ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
              MME.interchange
                (MME.interchange
                  (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
                  (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
                (MME.interchange
                  (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
                  (MME.StothersFourth.cwLiteralTermMonomial K q t₄))
          calc
            F (f₃ t₃) = ∑ t₂ : MME.StothersFourth.CWLiteralTerm q,
                F (f₂ t₂) := by
              dsimp only [f₃]
              exact map_sum F f₂ Finset.univ
            _ = 0 := by
              apply Fintype.sum_eq_zero
              intro t₂
              let f₁ := fun t₁ : MME.StothersFourth.CWLiteralTerm q =>
                MME.interchange
                  (MME.interchange
                    (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
                    (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
                  (MME.interchange
                    (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
                    (MME.StothersFourth.cwLiteralTermMonomial K q t₄))
              calc
                F (f₂ t₂) = ∑ t₁ : MME.StothersFourth.CWLiteralTerm q,
                    F (f₁ t₁) := by
                  dsimp only [f₂]
                  exact map_sum F f₁ Finset.univ
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  exact
                    mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight
                      q sigma hsum t₁ t₂ t₃ t₄
