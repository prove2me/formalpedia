-- Prove2me | solution 1 for linear_neumann_off_diagonal_contribution_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T15:41:56.061527+00:00
-- url     : https://prove2.me/submissions/849bc710-9db3-4133-9018-f8f9c50cb745

import Mathlib.Tactic
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_linear_neumann_correction_lambda_bound_le_one_eighth
import Theorems.Thm_linear_neumann_correction_lambda_sample_bound_from_general_bound
import Theorems.Thm_linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
import Theorems.Thm_linear_neumann_off_diagonal_decoupled_from_coefficient_bound
import Theorems.Thm_linear_neumann_off_diagonal_decoupling_transfer
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candès--Recht 2008, PDF p. 6, Theorem 1.3/equation (1.9), and PDF
pp. 27--29, equations (6.12)--(6.18).

This bridge follows the paper's off-diagonal proof:
1. use the repaired general-sample Lemma 6.6 coefficient estimate for `Q(E)`;
2. condition on the second sample and apply Theorem 6.3 to the outer sample;
3. combine the two-copy probability;
4. transfer the decoupled model back to the original Bernoulli model via
   Lemma 6.5.

The only lambda in this proof is an internal fixed large value chosen from the
full Theorem 1.3 sample lower bound.  It is not the obsolete standalone
lambda route with the wrong diagonal scale.
-/
theorem solution :
    ∃ Coff coff : ℝ, 0 < Coff ∧ 0 < coff ∧
      ∀ C' : ℝ, Coff ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) ≥
          1 - coff * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases linear_neumann_off_diagonal_coefficient_bound_under_general_sample_bound with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hCoef⟩
  rcases linear_neumann_off_diagonal_decoupled_from_coefficient_bound
      Cfixed hCfixed with
    ⟨Couter, couter, hCouter, hcouter, hOuter⟩
  rcases linear_neumann_off_diagonal_decoupling_transfer with
    ⟨Cdecouple, cdecouple, hCdecouple, hcdecouple, hDecouple⟩
  let Ascale : ℝ := 2 * (Cdecouple * (Couter * Ccoef))
  have hAscale : 0 < Ascale := by
    dsimp [Ascale]
    positivity
  rcases linear_neumann_correction_lambda_sample_bound_from_general_bound
      Ascale with
    ⟨Csample, hCsample, hSample⟩
  let Coff : ℝ := max Ccoef Csample
  refine ⟨Coff, cdecouple * (couter + ccoef), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hCcoef (le_max_left Ccoef Csample)
  · exact mul_pos hcdecouple (add_pos hcouter hccoef)
  · intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    let lam : ℝ := max 1 (8 * Ascale)
    have hlam : 1 ≤ lam := by
      dsimp [lam]
      exact le_max_left _ _
    have hCcoef_le : Ccoef ≤ C' :=
      le_trans (le_max_left Ccoef Csample) hC'
    have hCsample_le : Csample ≤ C' :=
      le_trans (le_max_right Ccoef Csample) hC'
    have hLambdaSample :=
      hSample C' hCsample_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hFixedSample :
        (m : ℝ) ≥
          β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
      linear_neumann_lambda_sample_lower_implies_fixed_matrix_sample_lower
        β lam n₁ n₂ r m μ₀ μ₁ hβ hlam hn₁ hn₂ hr hμ₀ hμ₁ hLambdaSample
    have hFixedAll :
        ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                CenteredSamplingSpectralBound Omega1
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Cfixed * Real.sqrt
                    ((β * (↑(max n₁ n₂)) *
                        Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
      intro X
      exact hFixed β hβ n₁ n₂ m X hn₁ hn₂ hm hFixedSample
    have hRep :
        ∀ Omega1 Omega2 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
      intro Omega1 Omega2
      exact linear_neumann_off_diagonal_decoupled_as_coefficient_fluctuation
        Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    have hCoefProb :=
      hCoef C' hCcoef_le β hβ n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    have hPairProb :=
      hOuter β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
        hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hLambdaSample
        hFixedAll hRep Ccoef ccoef hCcoef hccoef hCoefProb
    rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
      ⟨hpNonneg, hpLeOne⟩
    have hOriginalProb :=
      hDecouple S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (Couter * Ccoef) (couter + ccoef) β lam
        hpNonneg hpLeOne (mul_pos hCouter hCcoef) (add_pos hcouter hccoef)
        hPairProb
    have hSmall :
        (Cdecouple * (Couter * Ccoef)) * Real.rpow lam (-1) ≤
          (1 : ℝ) / 16 := by
      have hTwoSmall :
          Ascale * Real.rpow lam (-1) ≤ (1 : ℝ) / 8 := by
        dsimp [lam]
        exact linear_neumann_correction_lambda_bound_le_one_eighth
          Ascale hAscale
      have hTwoSmall' :
          2 * (Cdecouple * (Couter * Ccoef)) * Real.rpow lam (-1) ≤
            (1 : ℝ) / 8 := by
        simpa [Ascale, mul_assoc, mul_left_comm, mul_comm] using hTwoSmall
      nlinarith
    have hMono :
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Cdecouple * (Couter * Ccoef)) * Real.rpow lam (-1)) ≤
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (linearNeumannOffDiagonalContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (1 : ℝ) / 16) := by
      refine bernoulli_event_probability_mono
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) _ _
        hpNonneg hpLeOne ?_
      intro Omega hOmega
      exact le_trans hOmega hSmall
    exact le_trans hOriginalProb hMono
