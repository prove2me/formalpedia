-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_decoupled_from_coefficient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T02:01:22.19921+00:00
-- url     : https://prove2.me/submissions/91723222-0c62-45fb-a866-0b3dfb793866
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_outer_sampling_conditional_from_coefficient_bound
import Theorems.Thm_quadratic_neumann_last_index_distinct_centered_pair_probability_from_coefficient_and_outer_conditional_bound
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Split the final outer sampling step for the decoupled centered
`ω₁ = ω₂ ≠ ω₃` contribution into a fixed-`Ω₃` conditional sampling estimate
and a pair-product probability lift. -/
theorem solution
    (Cfixed : ℝ) :
    0 < Cfixed →
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
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
        (∀ Omega1 Omega3 : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
              Omega1 Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega1
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) →
        ∀ Ccoef ccoef : ℝ, 0 < Ccoef → 0 < ccoef →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticLastIndexDistinctCenteredCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega3 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - (couter + ccoef) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCfixed
  rcases
      quadratic_neumann_last_index_distinct_centered_outer_sampling_conditional_from_coefficient_bound
        Cfixed hCfixed with
    ⟨Ccond, ccond, hCcond, hccond, hConditional⟩
  rcases
      quadratic_neumann_last_index_distinct_centered_pair_probability_from_coefficient_and_outer_conditional_bound
        Ccond ccond hCcond hccond with
    ⟨Couter, couter, hCouter, hcouter, hPair⟩
  refine ⟨Couter, couter, hCouter, hcouter, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    hFixedAll hRep Ccoef ccoef hCcoef hccoef hCoefProb
  have hCondProb :
      ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticLastIndexDistinctCenteredCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Ccoef * Real.rpow lam (-1)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 =>
              spectralNorm
                (quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Ccond * Ccoef) * Real.rpow lam (-((3 : ℝ) / 2))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    intro Omega3 hCoefEvent
    have hRepFixed :
        ∀ Omega1 : Finset (Fin n₁ × Fin n₂),
          quadraticNeumannLastIndexDistinctCenteredDecoupledContribution
              Omega1 Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
            ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
                (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) •
              centeredSamplingFluctuation Omega1
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticLastIndexDistinctCenteredCoefficientMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
      intro Omega1
      exact hRep Omega1 Omega3
    exact hConditional β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hFixedAll
      Ccoef hCcoef Omega3 hCoefEvent hRepFixed
  exact hPair β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Ccoef ccoef hCcoef hccoef hCoefProb hCondProb
