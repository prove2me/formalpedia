-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_threshold_from_centered_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:25:51.193306+00:00
-- url     : https://prove2.me/submissions/952be71f-0e1d-469a-a4c4-6528dcc0602c

import Theorems.Thm_prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Specialize the generic quadratic mean-entry centered-fluctuation threshold
to the `ω₁ ≠ ω₂ = ω₃` mean contribution. -/
theorem solution
    (Cfixed Ccoef : ℝ) :
    0 < Cfixed → 0 < Ccoef →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
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
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannFirstIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) →
        entrySupNorm
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Ccoef * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
              (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticFirstIndexDistinctMeanCoefficientMatrix S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm
                (quadraticFirstIndexDistinctMeanCoefficientMatrix S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        spectralNorm
            (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCfixed hCcoef
  rcases
      prefactored_centered_sampling_fluctuation_quadratic_threshold_from_mean_entry_scale
        Cfixed Ccoef hCfixed hCcoef with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega hRep hEntry hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m μ₀
    hn₁ hn₂ hr hm hμ₀ hmLower Omega
    (quadraticFirstIndexDistinctMeanCoefficientMatrix S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    hRep hEntry hCentered
