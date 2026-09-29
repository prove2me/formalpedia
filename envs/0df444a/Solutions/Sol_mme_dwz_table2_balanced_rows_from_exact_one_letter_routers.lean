-- Prove2me | solution 1 for mme_dwz_table2_balanced_rows_from_exact_one_letter_routers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:38:18.838083+00:00
-- url     : https://prove2.me/submissions/ac5ea4fa-1ea3-4045-ad70-98cac8f70d69

import Theorems.Thm_mme_dwz_table2_balanced_rows_exact_allowed_dimension
import Theorems.Thm_mme_dwz_q6_balanced_allowed_card_six_finite_rate

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (h013 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 1 3 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 1 3)) =
          MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p,
            maps 2
                (((coarseClassBasis (K := K) 6 2 3).reindex
                  Equiv.ulift.symm) p) =
              (Pi.single (coord p, (0 : Fin 1)) 1 :
                Fin 12 × Fin 1 → K))
    (h031 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 0 3 1 s) →ₗ[K]
            (MMObj K 1 1 12).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 0 3 1)) =
          MMTensor K 1 1 12 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p,
            maps 2
                (((coarseClassBasis (K := K) 6 2 1).reindex
                  Equiv.ulift.symm) p) =
              (Pi.single (coord p, (0 : Fin 1)) 1 :
                Fin 12 × Fin 1 → K))
    (h103 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 1 0 3 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 1 0 3)) =
          MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
          ∀ p,
            maps 2
                (((coarseClassBasis (K := K) 6 2 3).reindex
                  Equiv.ulift.symm) p) =
              (Pi.single ((0 : Fin 1), coord p) 1 :
                Fin 1 × Fin 12 → K))
    (h301 :
      ∃ maps : ∀ s : Fin 3,
          (cwSquareCanonicalGrading K 6).classOf s
              (cwSquareBlockType 3 0 1 s) →ₗ[K]
            (MMObj K 12 1 1).V s,
        PiTensorProduct.map maps
            ((cwSquareCanonicalGrading K 6).blockTensor
              (cwSquareBlockType 3 0 1)) =
          MMTensor K 12 1 1 ∧
        ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
          ∀ p,
            maps 2
                (((coarseClassBasis (K := K) 6 2 1).reindex
                  Equiv.ulift.symm) p) =
              (Pi.single ((0 : Fin 1), coord p) 1 :
                Fin 1 × Fin 12 → K))
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
          ∃ a b c : ℕ,
            TensorObj.Restrict (MMObj K a b c)
              (restrictedComponentPower K s m) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
                    ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  rcases mme_dwz_q6_balanced_allowed_card_six_finite_rate tau htau with
    ⟨C, hC, hrate⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrate] with m hm
  intro s hs
  rcases mme_dwz_table2_balanced_rows_exact_allowed_dimension
      h013 h031 h103 h301 m s hs with ⟨a, b, c, hrestrict, hdim⟩
  refine ⟨a, b, c, hrestrict, ?_⟩
  have hr := hm s hs
  simpa only [hdim] using hr
