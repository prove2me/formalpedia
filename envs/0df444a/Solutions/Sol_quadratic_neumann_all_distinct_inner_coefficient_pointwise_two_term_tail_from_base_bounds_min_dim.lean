-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficient_pointwise_two_term_tail_from_base_bounds_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T13:36:48.504165+00:00
-- url     : https://prove2.me/submissions/c7dbc859-548a-4a67-b166-87671b96b50e

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales

open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Centry * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticAllDistinctInnerBaseMatrix S w1 w2) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint *
                    (Real.sqrt
                        ((β * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Cfro * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      ((β * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                        (Centry * μ₁ *
                          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hCentry _hCfrob
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hbern⟩
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1
    hrepr hentry hfrob w1 w2
  exact
    hbern β hβ n₁ n₂ m hn₁ hn₂ hm
      (fun Omega3 =>
        quadraticAllDistinctInnerCoefficient Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2)
      (quadraticAllDistinctInnerBaseMatrix S w1 w2)
      (Centry * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
      (Cfro * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
      (by
        intro Omega3
        exact hrepr Omega3 w1 w2)
      (hentry w1 w2)
      (hfrob w1 w2)
