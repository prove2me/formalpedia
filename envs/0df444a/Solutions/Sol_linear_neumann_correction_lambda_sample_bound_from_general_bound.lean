-- Prove2me | solution 1 for linear_neumann_correction_lambda_sample_bound_from_general_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:37:49.063725+00:00
-- url     : https://prove2.me/submissions/1e01dcc8-72b9-4997-bb75-8505d8777fb0

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (C₁ : ℝ) :
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
          max 1 (8 * C₁) * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) := by
  refine ⟨max 1 (max 1 (8 * C₁)), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ _hA0 _hA1 hmLower
    set n : ℕ := max n₁ n₂
    have hn_pos_nat : 0 < n := by
      dsimp [n]
      exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hn_real_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_real_pos
    have hr_real_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hn_pos_nat))
    have hbeta_nonneg : 0 ≤ β := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
    have htail_nonneg :
        0 ≤ (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
      positivity
    have hμ₁_nonneg : 0 ≤ μ₁ := le_trans (by norm_num) hμ₁
    have hCprime_ge_lambda : max 1 (8 * C₁) ≤ C' := by
      exact le_trans (le_max_right 1 (max 1 (8 * C₁))) hC'
    have hcoh_left :
        μ₁ * max (Real.sqrt μ₀) μ₁ ≤
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) := by
      by_cases hsqrt_le : Real.sqrt μ₀ ≤ μ₁
      · have hmax_eq : max (Real.sqrt μ₀) μ₁ = μ₁ := max_eq_right hsqrt_le
        rw [hmax_eq, sq]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      · have hμ₁_le_sqrt : μ₁ ≤ Real.sqrt μ₀ := le_of_lt (lt_of_not_ge hsqrt_le)
        have hmax_eq : max (Real.sqrt μ₀) μ₁ = Real.sqrt μ₀ := max_eq_left hμ₁_le_sqrt
        rw [hmax_eq, mul_comm μ₁ (Real.sqrt μ₀)]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hfactor :
        max 1 (8 * C₁) * (μ₁ * max (Real.sqrt μ₀) μ₁) ≤
          C' *
            max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) := by
      have hleft_nonneg : 0 ≤ max 1 (8 * C₁) := by
        exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 (8 * C₁))
      have hright_nonneg : 0 ≤ μ₁ * max (Real.sqrt μ₀) μ₁ := by
        positivity
      exact mul_le_mul hCprime_ge_lambda hcoh_left hright_nonneg (le_trans hleft_nonneg hCprime_ge_lambda)
    have hfactor_tail :
        max 1 (8 * C₁) * (μ₁ * max (Real.sqrt μ₀) μ₁) *
            ((n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) ≤
          C' *
            max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) *
            ((n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hfactor htail_nonneg
    have htarget_le_lower :
        max 1 (8 * C₁) * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂) : ℝ)) ≤
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂) : ℝ) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
      dsimp [n] at hfactor_tail
      nlinarith
    exact le_trans htarget_le_lower hmLower
