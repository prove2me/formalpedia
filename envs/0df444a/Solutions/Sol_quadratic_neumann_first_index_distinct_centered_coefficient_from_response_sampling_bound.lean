-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_coefficient_from_response_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:31:53.65988+00:00
-- url     : https://prove2.me/submissions/24c804cb-ef97-4822-900f-52862cfc6746

import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_coefficient_threshold_from_response_sampling_bound
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Lift the deterministic coefficient threshold for the
`ω₁ ≠ ω₂ = ω₃` centered quadratic term from individual samples to the Bernoulli
event probability supplied by fixed-matrix centered sampling. -/
theorem solution
    (Cfixed Cbase Cresp : ℝ) :
    0 < Cfixed → 0 < Cbase → 0 < Cresp →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            offDiagonalTangentResponse S
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S))) →
        (∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (offDiagonalTangentResponse S X) ≤
            Cresp * spectralNorm X) →
        entrySupNorm (linearNeumannDiagonalBaseMatrix S) ≤
          Cbase * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            entrySupNorm (signMatrix S) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              CenteredSamplingSpectralBound Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (linearNeumannDiagonalBaseMatrix S)
                (Cfixed * Real.sqrt
                  ((β * (↑(max n₁ n₂)) *
                      Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entrySupNorm (linearNeumannDiagonalBaseMatrix S))) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed hCbase hCresp
  rcases
      quadratic_neumann_first_index_distinct_centered_coefficient_threshold_from_response_sampling_bound
        Cfixed Cbase Cresp hCfixed hCbase hCresp with
    ⟨Cthreshold, hCthreshold, hThreshold⟩
  refine ⟨Cthreshold, 1, hCthreshold, zero_lt_one, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hRep hResponse hBase hFixedProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega2 =>
            CenteredSamplingSpectralBound Omega2 p
              (linearNeumannDiagonalBaseMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (linearNeumannDiagonalBaseMatrix S))) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S p
              (Cthreshold * Real.rpow lam (-1))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega2 hCentered
    exact hThreshold β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
      Omega2 (hRep Omega2) hResponse hBase hCentered
  exact le_trans hFixedProb hMono
