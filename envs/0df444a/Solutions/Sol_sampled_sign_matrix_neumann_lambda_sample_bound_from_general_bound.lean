-- Prove2me | solution 1 for sampled_sign_matrix_neumann_lambda_sample_bound_from_general_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T19:25:28.453155+00:00
-- url     : https://prove2.me/submissions/68b3bdf8-ddf3-43e5-bf1e-5ecbec6158ef

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem solution
    (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
          max 1 ((8 * C₀) ^ 2) * μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) := by
  refine ⟨max 1 ((8 * C₀) ^ 2), by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1 hgen
  refine le_trans ?_ hgen
  have hmaxn1 : (1:ℝ) ≤ (↑(max n₁ n₂)) := by
    have : 1 ≤ max n₁ n₂ := le_max_of_le_left hn1
    exact_mod_cast this
  have hlog : 0 ≤ Real.log (↑(max n₁ n₂)) := Real.log_nonneg hmaxn1
  have hbl : 0 ≤ β * Real.log (↑(max n₁ n₂)) := by positivity
  have hμ1sq : μ₁ ^ 2 ≤
      max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁)) (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1:ℝ)/4)) :=
    le_max_of_le_left (le_max_left _ _)
  have hC'0 : (0:ℝ) ≤ C' := le_trans (by positivity) hC'
  gcongr
