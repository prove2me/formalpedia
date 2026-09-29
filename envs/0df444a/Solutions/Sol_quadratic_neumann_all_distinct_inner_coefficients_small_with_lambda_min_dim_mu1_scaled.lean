-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda_min_dim_mu1_scaled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-02T17:44:09.291789+00:00
-- url     : https://prove2.me/submissions/ae7900e2-c236-4337-9020-db3eb5d37cff

import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_mu1_scaled
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation

open MatrixCompletion

/-!
Sound `μ₁`-explicit, `min(n₁,n₂)`-denominator restatement of the all-distinct
inner coefficient bound `quadratic_neumann_all_distinct_inner_coefficients_small_with_lambda`
(the free-`μ₁` node was unsound: dropping `μ₁` from the conclusion fails the
`‖G‖_∞ ≤ C √(μ₀ n r β log n / m) ‖E‖_∞`, `‖E‖_∞ ≤ μ₁ √(r/n)` estimate of CR §6.3
eq (6.23)).

This node mirrors the Proved middle-index template
`quadratic_neumann_middle_index_distinct_centered_coefficient_bound_small_with_lambda_min_dim_shifted`:
it carries an extra `(β+4)·log N` shifted-density hypothesis and reduces, through the
kernel-square / Bernstein-pointwise combiner, onto the Proved `min`-denominator base
suppliers and the Proved fluctuation identity.

Source: Candès--Recht 2008, Section 6.3, equations (6.20), (6.23) and
Lemma 6.6 equations (6.15)--(6.17).
-/

theorem solution :
    ∃ Cinner cinner : ℝ, 0 < Cinner ∧ 0 < cinner ∧
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
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cinner * μ₁ *
                    Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) := by
  -- Proved min-dimension base suppliers.
  rcases quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hEntrySup⟩
  rcases quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hFrobNorm⟩
  -- The kernel-square / Bernstein-pointwise combiner specialised to these constants.
  rcases quadratic_neumann_all_distinct_inner_coefficients_from_base_bounds_min_dim_mu1_scaled
      Centry Cfro hCentry hCfro with
    ⟨Cinner, cinner, hCinner, hcinner, hCombiner⟩
  refine ⟨Cinner, cinner, hCinner, hcinner, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift
  -- discharge the fluctuation identity hypothesis.
  have hRep :
      ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (w1 w2 : Fin n₁ × Fin n₂),
        quadraticAllDistinctInnerCoefficient Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
          matrixEntrySum
            (centeredSamplingFluctuation Omega3
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (quadraticAllDistinctInnerBaseMatrix S w1 w2)) := by
    intro Omega3 w1 w2
    exact quadratic_neumann_all_distinct_inner_coefficient_as_centered_scalar_fluctuation
      Omega3 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2
  -- discharge the min-dimension base bounds.
  have hEntry :
      ∀ w1 w2 : Fin n₁ × Fin n₂,
        entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    intro w1 w2
    exact hEntrySup n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  have hFrob :
      ∀ w1 w2 : Fin n₁ × Fin n₂,
        frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
          Cfro * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    intro w1 w2
    exact hFrobNorm n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w1 w2
  exact hCombiner β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower hmShift hRep hEntry hFrob
