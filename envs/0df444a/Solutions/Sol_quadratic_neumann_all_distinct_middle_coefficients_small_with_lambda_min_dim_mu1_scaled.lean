-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_small_with_lambda_min_dim_mu1_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T17:47:21.027093+00:00
-- url     : https://prove2.me/submissions/f92bfbb2-ac78-4cce-8d59-0c032424e195

import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled
import Theorems.Thm_quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted

open MatrixCompletion

/-!
Corrected `μ₁`-explicit all-distinct middle-coefficient wrapper.

This is a formal bridge from the corrected inner coefficient estimate and the
corrected middle-from-inner decoupling estimate.  It is not a verbatim theorem
in Candes-Recht; it packages the two source-backed Section 6.3 steps needed for
the all-distinct quadratic Neumann branch.

Source: Candes-Recht 2008, Section 6.3, PDF p. 30 equation (6.20), PDF p. 31
Lemma 6.8 equations (6.22)--(6.23), and PDF pp. 28--29 Lemma 6.6 equations
(6.15)--(6.17).
-/

theorem solution :
    ∃ Cmid cmid : ℝ, 0 < Cmid ∧ 0 < cmid ∧
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
              ((β + 4) * Real.log (↑(max n₁ n₂))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cmid * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-1))) ≥
          1 - cmid * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled with
    ⟨Cinner, cinner, hCinner, hcinner, hInner⟩
  rcases quadratic_neumann_all_distinct_middle_from_inner_coefficient_bound_min_dim_shifted with
    ⟨Cstep, cstep, hCstep, hcstep, hStep⟩
  refine ⟨Cstep * Cinner, cstep + cinner,
    mul_pos hCstep hCinner, add_pos hcstep hcinner, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift
  have hInnerProb :=
    hInner β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift
  exact hStep β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift
    Cinner cinner hCinner hcinner hInnerProb
