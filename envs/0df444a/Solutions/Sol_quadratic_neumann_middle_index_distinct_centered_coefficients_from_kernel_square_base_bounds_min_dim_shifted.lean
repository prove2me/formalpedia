-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T19:11:26.54086+00:00
-- url     : https://prove2.me/submissions/f5282dac-3861-46a0-8490-f5f8503095b7

import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
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
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 2) * Real.log (↑(max n₁ n₂))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          ∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2 =
            signMatrix S w1.1 w1.2 *
              matrixEntrySum
                (centeredSamplingFluctuation Omega2
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(min n₁ n₂))) ^ 2)) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfrob
  rcases
      quadratic_neumann_middle_index_distinct_centered_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
        Centry Cfro hCentry hCfrob with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩
  rcases
      quadratic_neumann_middle_index_distinct_centered_coefficients_uniform_from_shifted_pointwise_tails
        Cpoint cpoint hCpoint hcpoint with
    ⟨Ccoef, ccoef, hCcoef, hccoef, huniform⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    hsampleβ hsampleβ2 hrepr hentry hfrob
  refine
    huniform β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
      hsampleβ ?_
  intro w1
  exact
    hpoint (β + 2) lam (by linarith) hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsampleβ2 w1
      (hrepr w1) (hentry w1) (hfrob w1)
