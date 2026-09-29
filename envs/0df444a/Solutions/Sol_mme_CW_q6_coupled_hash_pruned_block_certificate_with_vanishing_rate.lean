-- Prove2me | solution 1 for mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:58:01.351432+00:00
-- url     : https://prove2.me/submissions/b2162904-dcc0-4a49-881a-b9fe0f77a653
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ rate : ℕ → ℝ,
      (∀ N, 0 ≤ rate N) ∧
      Tendsto rate atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let Gcount : ℕ := N - L
        let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
        ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
            (C : Finset (Fin 3 → Fin t))
            (σs : Fin C.card → (Fin 3 → Fin t)),
          TensorObj.Restrict P
              ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (∀ j, σs j ∈ C) ∧
          Function.Injective σs ∧
          (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
            ∀ i : Fin 3, σ i ≠ σ' i) ∧
          (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
          (∀ j, TensorObj.Restrict
            (coupledQ6Survivor K L Gcount)
            (grading.blockSubtensor (σs j))) ∧
          (raw * Real.exp (-rate N)) ^ (2 * N) ≤
            (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  let rate : ℕ → ℝ := fun N =>
    (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
  have hcast :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hsqrt_sqrt :
      Tendsto
        (fun N : ℕ => Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hsqrt
  refine ⟨rate, ?_, ?_, ?_⟩
  · intro N
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · exact tendsto_inv_atTop_zero.comp hsqrt_sqrt
  · simpa only [rate] using
      mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss
        (K := K) tau htau
