-- Prove2me | solution 1 for quadratic_neumann_all_distinct_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:49.660743+00:00
-- url     : https://prove2.me/submissions/b21c259d-eff1-41f1-b9cd-d0d4fa8f4b72

import Theorems.Thm_quadratic_neumann_all_distinct_decoupled_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_distinct_from_decoupled_bound
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Decompose the all-distinct term of Lemma 4.6 through triple decoupling and
the decoupled Bernstein/sampling estimate. -/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllDistinctContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_distinct_decoupled_contribution_small_with_lambda with
    ⟨Cdec, cdec, hCdec, hcdec, hDecoupled⟩
  rcases quadratic_neumann_all_distinct_from_decoupled_bound with
    ⟨K, L, hK, hL, hTransfer⟩
  refine ⟨K * Cdec, L * cdec, mul_pos hK hCdec, mul_pos hL hcdec, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hDecoupledProb :=
    hDecoupled β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  exact hTransfer S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    Cdec cdec β lam hpNonneg hpLeOne hCdec hcdec hDecoupledProb
