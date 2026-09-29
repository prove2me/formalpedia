-- Prove2me | solution 1 for linear_neumann_off_diagonal_pair_probability_from_coefficient_and_outer_conditional_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:08:00.537951+00:00
-- url     : https://prove2.me/submissions/e287c1ab-1f74-4f4a-92e7-284ab85b9f38

import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Specialize the reusable two-copy Bernoulli product lift to the decoupled
off-diagonal linear Neumann term. -/
theorem solution
    (Ccond ccond : ℝ) :
    0 < Ccond → 0 < ccond →
    ∃ Couter couter : ℝ, 0 < Couter ∧ 0 < couter ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Ccoef ccoef : ℝ, 0 < Ccoef → 0 < ccoef →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) →
        (∀ Omega2 : Finset (Fin n₁ × Fin n₂),
          LinearNeumannOffDiagonalCoefficientBound Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (Ccoef * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                        (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))) →
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega1 =>
                spectralNorm
                  (linearNeumannOffDiagonalDecoupledContribution
                    Omega1 Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                  (Ccond * Ccoef) * Real.rpow lam (-1)) ≥
            1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β)) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (linearNeumannOffDiagonalDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (Couter * Ccoef) * Real.rpow lam (-1)) ≥
          1 - (couter + ccoef) *
            Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCcond hccond
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    Ccoef ccoef _hCcoef _hccoef hCoefProb hCondProb
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
      p ccoef ccond (Real.rpow (↑(max n₁ n₂)) (-β))
      (fun Omega2 =>
        LinearNeumannOffDiagonalCoefficientBound Omega2 S p
          (Ccoef * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))))
      (fun Omega1 Omega2 =>
        spectralNorm
          (linearNeumannOffDiagonalDecoupledContribution Omega1 Omega2 S p) ≤
          (Ccond * Ccoef) * Real.rpow lam (-1))
      hp.1 hp.2 hFailureNonneg hCoefProb hCondProb
