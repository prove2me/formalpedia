-- Prove2me | solution 1 for mme_stothers_phi116_four_edge_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:28:37.67745+00:00
-- url     : https://prove2.me/submissions/ec31f317-ea94-4d7c-aa1b-c20e6f586e47

import Theorems.Thm_mme_stothers_phi116_four_term_projection_zero
import Theorems.Thm_mme_stothers_phi116_fourth_tensor_term_expansion

open MME TensorProduct Module BigOperators
open MME.StothersFourth
open MME.StothersFourth.Phi116

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem linearMap_pair_fintype_sum
    {R : Type*} [Semiring R]
    {iota M N P : Type*} [Fintype iota]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : iota → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

theorem solution
    {K : Type u} [Field K] :
    ∀ sigma : Fin 3 → Fin 3,
      sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
      sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
      (cwPhi116ThreeGrading K).blockTensor sigma = 0 := by
  intro sigma h000 h111 h012 h102
  unfold TensorObj.TypeGrading.blockTensor
  change
    PiTensorProduct.map
        (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K 6).blockProj s
            (phi116ModeTotalGrade s))
          (cwFourthObj K 6).t) = 0
  rw [mme_stothers_phi116_fourth_tensor_term_expansion]
  let A := PiTensorProduct.map
    (fun s => (cwPhi116ThreeGrading K).blockProj s (sigma s))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K 6).blockProj s
      (phi116ModeTotalGrade s))
  let f₄ := fun t₄ : CWTerm 6 =>
    ∑ t₃ : CWTerm 6, ∑ t₂ : CWTerm 6, ∑ t₁ : CWTerm 6,
      interchange
        (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
        (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄))
  calc
    _ = ∑ t₄ : CWTerm 6, A (B (f₄ t₄)) := by
      exact linearMap_pair_fintype_sum A B f₄
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t₄
      let f₃ := fun t₃ : CWTerm 6 =>
        ∑ t₂ : CWTerm 6, ∑ t₁ : CWTerm 6,
          interchange
            (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
            (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄))
      calc
        A (B (f₄ t₄)) =
            ∑ t₃ : CWTerm 6, A (B (f₃ t₃)) := by
          dsimp only [f₄]
          exact linearMap_pair_fintype_sum A B f₃
        _ = 0 := by
          apply Fintype.sum_eq_zero
          intro t₃
          let f₂ := fun t₂ : CWTerm 6 =>
            ∑ t₁ : CWTerm 6,
              interchange
                (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
                (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄))
          calc
            A (B (f₃ t₃)) =
                ∑ t₂ : CWTerm 6, A (B (f₂ t₂)) := by
              dsimp only [f₃]
              exact linearMap_pair_fintype_sum A B f₂
            _ = 0 := by
              apply Fintype.sum_eq_zero
              intro t₂
              let f₁ := fun t₁ : CWTerm 6 =>
                interchange
                  (interchange (cwTermMonom K 6 t₁) (cwTermMonom K 6 t₂))
                  (interchange (cwTermMonom K 6 t₃) (cwTermMonom K 6 t₄))
              calc
                A (B (f₂ t₂)) =
                    ∑ t₁ : CWTerm 6, A (B (f₁ t₁)) := by
                  dsimp only [f₂]
                  exact linearMap_pair_fintype_sum A B f₁
                _ = 0 := by
                  apply Fintype.sum_eq_zero
                  intro t₁
                  dsimp only [A, B, f₁]
                  exact mme_stothers_phi116_four_term_projection_zero
                    K sigma h000 h111 h012 h102 t₁ t₂ t₃ t₄
