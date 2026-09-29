-- Prove2me | solution 1 for quadratic_neumann_all_equal_centered_fixed_matrix_sampling_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T01:55:12.170537+00:00
-- url     : https://prove2.me/submissions/c263315c-1d38-458a-8424-1f23f0e6ee6b

import Theorems.Thm_quadratic_neumann_all_equal_centered_threshold_from_centered_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Transfer the fixed-matrix centered sampling event to the centered all-equal
quadratic contribution by pointwise deterministic threshold absorption and
Bernoulli event monotonicity. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Ccent ccent : ℝ, 0 < Ccent ∧ 0 < ccent ∧
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
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannAllEqualCenteredContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
              centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)) →
        entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
          Cbase * μ₀ ^ 3 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 3) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticNeumannAllEqualBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                Ccent * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccent * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed hCbase
  rcases
      quadratic_neumann_all_equal_centered_threshold_from_centered_sampling_bound
        Cfixed Cbase hCfixed hCbase with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hRep hBase hFixedProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p
              (quadraticNeumannAllEqualBaseMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
              Cthreshold * Real.rpow lam (-((3 : ℝ) / 2))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Omega (hRep Omega) hBase hCentered
  exact le_trans hFixedProb hMono
