-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_mean_threshold_from_response_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:29:32.525255+00:00
-- url     : https://prove2.me/submissions/33f3fdc3-bc00-4305-82bb-04ea8cc38733

import Theorems.Thm_response_centered_sampling_quadratic_mean_threshold_from_rescaled_sign_event
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Specialize the generic rescaled-sign response threshold to the
`ω₁ = ω₂ ≠ ω₃` mean contribution. -/
theorem solution
    (Cfixed Cresp : ℝ) :
    0 < Cfixed → 0 < Cresp →
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
        quadraticNeumannLastIndexDistinctMeanContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          (1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) •
            quadraticLastIndexDistinctOffDiagonalResponse S
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                  signMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) * spectralNorm X) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
              signMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm
                ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                  signMatrix S)) →
        spectralNorm
            (quadraticNeumannLastIndexDistinctMeanContribution Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCfixed hCresp
  rcases response_centered_sampling_quadratic_mean_threshold_from_rescaled_sign_event
      Cfixed Cresp hCfixed hCresp with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega hRep hResponse hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower Omega
    (quadraticNeumannLastIndexDistinctMeanContribution Omega S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    (quadraticLastIndexDistinctOffDiagonalResponse S) hRep hResponse hCentered
