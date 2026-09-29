-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_pair_probability_from_inner_and_conditional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:08:02.999528+00:00
-- url     : https://prove2.me/submissions/08e69fee-20a9-45d1-8132-0f6828ef53af

import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Specialize the reusable two-copy Bernoulli product lift to the
all-distinct middle coefficient transfer from the inner coefficient event. -/
theorem solution
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Cstep cstep : ℝ, 0 < Cstep ∧ 0 < cstep ∧
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
        ∀ Cinner cinner : ℝ, 0 < Cinner → 0 < cinner →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega3 =>
              QuadraticAllDistinctInnerCoefficientBound Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Cinner * Real.rpow lam (-((1 : ℝ) / 2)))) ≥
          1 - cinner * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega3 : Finset (Fin n₁ × Fin n₂),
          QuadraticAllDistinctInnerCoefficientBound Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 Omega3 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Cstep * Cinner) * Real.rpow lam (-1))) ≥
          1 - (cstep + cinner) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCcond hccond
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam _hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    Cinner cinner _hCinner _hcinner hInnerProb hCondProb
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hFailureNonneg :
      0 ≤ ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
    have hmax_pos_nat : 0 < max n₁ n₂ :=
      lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hmax_pos : 0 < (↑(max n₁ n₂) : ℝ) := by
      exact_mod_cast hmax_pos_nat
    exact mul_nonneg (le_of_lt hccond)
      (le_of_lt (Real.rpow_pos_of_pos hmax_pos (-β)))
  exact
    bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
      p cinner ccond (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega3 =>
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p
          (Cinner * Real.rpow lam (-((1 : ℝ) / 2))))
      (fun Omega2 Omega3 =>
        QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p
          ((Ccond * Cinner) * Real.rpow lam (-1)))
      hp.1 hp.2 hFailureNonneg hInnerProb hCondProb
