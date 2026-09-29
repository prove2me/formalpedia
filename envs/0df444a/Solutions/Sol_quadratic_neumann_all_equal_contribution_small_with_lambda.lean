-- Prove2me | solution 1 for quadratic_neumann_all_equal_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T00:42:27.868974+00:00
-- url     : https://prove2.me/submissions/538084cc-b55d-42c3-be6d-168e30e05257

import Theorems.Thm_quadratic_neumann_all_equal_centered_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_equal_mean_contribution_small_with_lambda
import Theorems.Thm_quadratic_neumann_all_equal_bound_from_centered_and_mean_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Split the all-equal quadratic term using the cubic centered-indicator
identity in equation (6.21), then combine the random centered estimate with the
deterministic mean estimate. -/
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
                (quadraticNeumannAllEqualContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                C * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_equal_centered_contribution_small_with_lambda with
    ⟨Ccent, ccent, hCcent, hccent, hCentered⟩
  rcases quadratic_neumann_all_equal_mean_contribution_small_with_lambda with
    ⟨Cmean, hCmean, hMean⟩
  refine ⟨Ccent + Cmean, ccent,
    add_pos hCcent hCmean, hccent, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hCenteredProb :=
    hCentered β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hMeanBound :=
    hMean β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hpNonneg, hpLeOne⟩
  have hMono :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllEqualCenteredContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≤
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllEqualContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              (Ccent + Cmean) * Real.rpow lam (-((3 : ℝ) / 2))) :=
    bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega =>
        spectralNorm
          (quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccent * Real.rpow lam (-((3 : ℝ) / 2)))
      (fun Omega =>
        spectralNorm
          (quadraticNeumannAllEqualContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (Ccent + Cmean) * Real.rpow lam (-((3 : ℝ) / 2)))
      hpNonneg hpLeOne
      (by
        intro Omega hCenteredBound
        exact quadratic_neumann_all_equal_bound_from_centered_and_mean_bounds
          S Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          Ccent Cmean lam hCenteredBound hMeanBound)
  exact le_trans hCenteredProb hMono
