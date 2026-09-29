-- Prove2me | solution 1 for linear_neumann_off_diagonal_decoupling_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:25:33.940109+00:00
-- url     : https://prove2.me/submissions/59b524c8-101c-4f5f-a94c-991e683bebdb

import Theorems.Thm_linear_neumann_off_diagonal_pair_decoupling_tail_bound
import Theorems.Thm_linear_neumann_off_diagonal_original_tail_from_diagonal_decoupled_tail

open MatrixCompletion

/-- Prove the off-diagonal first-order decoupling transfer from the
threshold-form pair-decoupling tail bound and the diagonal-coupling transfer. -/
theorem solution :
    ∃ Cdecouple cdecouple : ℝ, 0 < Cdecouple ∧ 0 < cdecouple ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r) (p Cdec cdec β lam : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S p) ≤
                Cdec * Real.rpow lam (-1)) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S p) ≤
                (Cdecouple * Cdec) * Real.rpow lam (-1)) ≥
          1 - (cdecouple * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_off_diagonal_pair_decoupling_tail_bound with
    ⟨K, L, hK, hL, hPair⟩
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec β lam hp0 hp1 hCdec hcdec hDecoupled
  have hDiagonal :=
    hPair S p Cdec cdec
      (Real.rpow (↑(max n₁ n₂)) (-β)) (Real.rpow lam (-1))
      hp0 hp1 hCdec hcdec hDecoupled
  exact
    linear_neumann_off_diagonal_original_tail_from_diagonal_decoupled_tail
      S p ((K * Cdec) * Real.rpow lam (-1))
      (1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β))
      hp0 hp1 hDiagonal
