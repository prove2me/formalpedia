-- Prove2me | solution 1 for mme_CW_block_dimension_products
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T22:47:42.003318+00:00
-- url     : https://prove2.me/submissions/847bf64a-737b-4b91-8d2d-9e50ae97c2f6

import Theorems.Thm_mme_CW_block_kronPow_MM_corrected

open BigOperators

theorem solution (q N : ℕ) (τ : Fin N → Fin 3 × Fin 3 × Fin 3) :
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).1) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 0, 1))).card ∧
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.1) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (1, 1, 0))).card ∧
    (∏ k : Fin N, (cwBlockMMDim (τ k) q).2.2) =
        q ^ (Finset.univ.filter (fun k : Fin N => τ k = (0, 1, 1))).card := by
  have hx (k : Fin N) :
      (cwBlockMMDim (τ k) q).1 = if τ k = (1, 0, 1) then q else 1 := by
    simp only [cwBlockMMDim]
    split_ifs <;> simp_all
  have hy (k : Fin N) :
      (cwBlockMMDim (τ k) q).2.1 = if τ k = (1, 1, 0) then q else 1 := by
    simp only [cwBlockMMDim]
    split_ifs <;> simp_all
  have hz (k : Fin N) :
      (cwBlockMMDim (τ k) q).2.2 = if τ k = (0, 1, 1) then q else 1 := by
    simp only [cwBlockMMDim]
    split_ifs <;> simp_all
  constructor
  · simp_rw [hx]
    simp [Finset.prod_ite]
  · constructor
    · simp_rw [hy]
      simp [Finset.prod_ite]
    · simp_rw [hz]
      simp [Finset.prod_ite]
