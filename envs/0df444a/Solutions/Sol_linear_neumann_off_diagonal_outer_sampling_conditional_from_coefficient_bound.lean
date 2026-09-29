-- Prove2me | solution 1 for linear_neumann_off_diagonal_outer_sampling_conditional_from_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:49:46.843147+00:00
-- url     : https://prove2.me/submissions/84b2299d-6961-49cf-9ce7-532aedfcae82

import Theorems.Thm_linear_neumann_off_diagonal_decoupled_threshold_from_centered_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Prove the fixed-`Ω₂` outer sampling conditional estimate for the
off-diagonal linear Neumann term by applying the fixed-matrix centered sampling
theorem to the conditional coefficient matrix and then using deterministic
threshold absorption. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
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
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                CenteredSamplingSpectralBound Omega1
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X
                  (Cfixed * Real.sqrt
                    ((β * (↑(max n₁ n₂)) *
                        Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entrySupNorm X)) ≥
            1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β)) →
        ∀ Ccoef : ℝ, 0 < Ccoef →
        ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
        LinearNeumannOffDiagonalCoefficientBound Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                      (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) →
        (∀ Omega1 : Finset (Fin n₁ × Fin n₂),
          linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            centeredSamplingFluctuation Omega1
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Ccond * Ccoef) * Real.rpow lam (-1)) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed
  rcases
      linear_neumann_off_diagonal_decoupled_threshold_from_centered_sampling_bound
        Cfixed hCfixed with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll Ccoef hCcoef Omega2 hCoefEvent hRep
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let X : Matrix (Fin n₁) (Fin n₂) ℝ :=
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p
  have hFixedProb :
      bernoulliEventProb p
          (fun Omega1 =>
            CenteredSamplingSpectralBound Omega1 p X
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm X)) ≥
        1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    exact hFixedAll X
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega1 =>
            CenteredSamplingSpectralBound Omega1 p X
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm X)) ≤
        bernoulliEventProb p
          (fun Omega1 =>
            spectralNorm
              (linearNeumannOffDiagonalDecoupledContribution
                Omega1 Omega2 S p) ≤
              (Cthreshold * Ccoef) * Real.rpow lam (-1)) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega1 hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Ccoef hCcoef Omega1 Omega2 hCoefEvent (hRep Omega1) hCentered
  exact le_trans hFixedProb hMono
