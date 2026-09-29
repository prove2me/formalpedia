-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_coefficient_threshold_from_response_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T04:56:17.074329+00:00
-- url     : https://prove2.me/submissions/3014b737-2a71-45ef-8bd7-aac20ccd313e

import Theorems.Thm_response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Specialize the generic deterministic response threshold with an explicit
base entry scale to the centered `ω₁ ≠ ω₂ = ω₃` coefficient matrix. -/
theorem solution
    (Cfixed Cbase Cresp : ℝ) :
    0 < Cfixed → 0 < Cbase → 0 < Cresp →
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
        ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
        quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
          offDiagonalTangentResponse S
            (centeredSamplingFluctuation Omega2
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (linearNeumannDiagonalBaseMatrix S)) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (offDiagonalTangentResponse S X) ≤
            Cresp * spectralNorm X) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            entrySupNorm (signMatrix S) →
        CenteredSamplingSpectralBound Omega2
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (linearNeumannDiagonalBaseMatrix S)
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm (linearNeumannDiagonalBaseMatrix S)) →
        QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (Cthreshold * Real.rpow lam (-1)) := by
  intro hCfixed hCbase hCresp
  rcases
      response_centered_sampling_quadratic_coefficient_threshold_from_base_entry_scale
        Cfixed Cbase Cresp hCfixed hCbase hCresp with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, hCthreshold, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Omega2 hRep hResponse hBase hCentered
  exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower Omega2
    (linearNeumannDiagonalBaseMatrix S)
    (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))
    (offDiagonalTangentResponse S) hRep hResponse hBase hCentered
