-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficient_pointwise_tail_from_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:24:05.584704+00:00
-- url     : https://prove2.me/submissions/52426c8a-e505-42a2-a09f-19010f831f36

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_with_inner_scale_from_entry_frobenius_bounds
import Definitions.Def_matrix_completion_neumann

open MatrixCompletion


open MatrixCompletion

/-- Specialize the generic conditional scalar Bernstein estimate to the middle
`H_{ω₁}` coefficient after the inner all-distinct coefficient has been
controlled. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
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
        ∀ Cinner : ℝ, 0 < Cinner →
        ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
        ∀ w1 : Fin n₁ × Fin n₂,
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega2
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctMiddleBaseMatrix Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1))) →
        entrySupNorm
            (quadraticAllDistinctMiddleBaseMatrix Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
          Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
            μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) →
        frobeniusNorm
            (quadraticAllDistinctMiddleBaseMatrix Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1) ≤
          Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
            Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂)))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                (Cpoint * Cinner) * Real.rpow lam (-1)) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases
      scalar_centered_sampling_bernstein_tail_with_inner_scale_from_entry_frobenius_bounds
        Centry Cfro hCentry hCfro with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hScalar⟩
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
    Cinner hCinner Omega3 hInnerEvent w1 hRep hEntry hFrob
  exact hScalar β lam hβ hlam n₁ n₂ r m μ₀ Cinner
    hn₁ hn₂ hr hm hμ₀ hCinner hmLower
    (fun Omega2 =>
      quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1)
    (quadraticAllDistinctMiddleBaseMatrix Omega3 S
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1)
    hRep hEntry hFrob
