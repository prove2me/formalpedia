-- Prove2me | solution 1 for quadratic_neumann_all_distinct_from_decoupled_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:51.145962+00:00
-- url     : https://prove2.me/submissions/2d5a214e-b7e7-4905-a92e-145b2fffe691

import Theorems.Thm_quadratic_neumann_all_distinct_triple_decoupling_tail_bound
import Theorems.Thm_quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail

open MatrixCompletion

/-- Prove the all-distinct transfer from the threshold-form triple-decoupling
tail bound and the diagonal-coupling-to-original tail transfer. -/
theorem solution
    : ∃ K L : ℝ, 0 < K ∧ 0 < L ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
        (p Cdec cdec β lam : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec →
        bernoulliTripleEventProb p
            (fun Omega1 Omega2 Omega3 =>
              spectralNorm
                (quadraticNeumannAllDistinctDecoupledContribution
                  Omega1 Omega2 Omega3 S p) ≤
                Cdec * Real.rpow lam (-((3 : ℝ) / 2))) ≥
            1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm (quadraticNeumannAllDistinctContribution Omega S p) ≤
                (K * Cdec) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_distinct_triple_decoupling_tail_bound with
    ⟨K, L, hK, hL, hTriple⟩
  refine ⟨K, L, hK, hL, ?_⟩
  intro n₁ n₂ r M S p Cdec cdec β lam hp0 hp1 hCdec hcdec hDecoupled
  have hDiagonal :=
    hTriple S p Cdec cdec
      (Real.rpow (↑(max n₁ n₂)) (-β))
      (Real.rpow lam (-((3 : ℝ) / 2)))
      hp0 hp1 hCdec hcdec hDecoupled
  exact
    quadratic_neumann_all_distinct_original_tail_from_diagonal_decoupled_tail
      S p ((K * Cdec) * Real.rpow lam (-((3 : ℝ) / 2)))
      (1 - (L * cdec) * Real.rpow (↑(max n₁ n₂)) (-β))
      hp0 hp1 hDiagonal
