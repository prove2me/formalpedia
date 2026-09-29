-- Prove2me | solution 1 for linear_neumann_diagonal_contribution_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T04:25:33.19751+00:00
-- url     : https://prove2.me/submissions/62598b4e-9206-4bb5-af05-fc63fe14ecd7

import Theorems.Thm_linear_neumann_diagonal_centered_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_diagonal_mean_contribution_small_with_lambda
import Theorems.Thm_linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Split the diagonal first-order contribution by (6.9): the centered random
part is controlled probabilistically, and the mean part deterministically. -/
theorem solution :
    ∃ Cdiag cdiag : ℝ, 0 < Cdiag ∧ 0 < cdiag ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Cdiag * Real.rpow lam (-1)) ≥
          1 - cdiag * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases linear_neumann_diagonal_centered_contribution_small_with_lambda with
    ⟨Ccenter, ccenter, hCcenter, hccenter, hCenter⟩
  rcases linear_neumann_diagonal_mean_contribution_small_with_lambda with
    ⟨Cmean, hCmean, hMean⟩
  refine ⟨Ccenter + Cmean, ccenter,
    add_pos hCcenter hCmean, hccenter, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  have hCenterProb :=
    hCenter β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
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
              (linearNeumannDiagonalCenteredContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              Ccenter * Real.rpow lam (-1)) ≤
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            spectralNorm
              (linearNeumannDiagonalContribution Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
              (Ccenter + Cmean) * Real.rpow lam (-1)) :=
    bernoulli_event_probability_mono
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
      (fun Omega =>
        spectralNorm
          (linearNeumannDiagonalCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccenter * Real.rpow lam (-1))
      (fun Omega =>
        spectralNorm
          (linearNeumannDiagonalContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          (Ccenter + Cmean) * Real.rpow lam (-1))
      hpNonneg hpLeOne
      (by
        intro Omega hCenteredBound
        exact linear_neumann_diagonal_contribution_bound_from_centered_and_mean_bounds
          S Omega ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          Ccenter Cmean lam hCenteredBound hMeanBound)
  exact le_trans hCenterProb hMono
