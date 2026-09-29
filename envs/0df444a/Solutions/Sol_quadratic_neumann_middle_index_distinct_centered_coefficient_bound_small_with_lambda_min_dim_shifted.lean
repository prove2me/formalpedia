-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficient_bound_small_with_lambda_min_dim_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T19:24:38.282342+00:00
-- url     : https://prove2.me/submissions/53925536-028b-40e5-bd30-e27a823f9091

import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficient_entry_as_signed_scalar_fluctuation
import Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

theorem solution :
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hentry⟩
  rcases quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hfrob⟩
  rcases
      quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds_min_dim_shifted
        Centry Cfro hCentry hCfro with
    ⟨Ccoef, ccoef, hCcoef, hccoef, hbridge⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    hsampleβ hsampleβ2
  refine
    hbridge β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
      hsampleβ hsampleβ2 ?_ ?_ ?_
  · intro w1 Omega2
    exact
      quadratic_neumann_middle_index_distinct_centered_coefficient_entry_as_signed_scalar_fluctuation
        Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1
  · intro w1
    exact hentry n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1
  · intro w1
    exact hfrob n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1
