-- Prove2me | solution 1 for tangent_sampling_deviation_scale_from_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T14:55:28.540356+00:00
-- url     : https://prove2.me/submissions/747a2a7c-bd19-4139-9bf8-b5c4f6336b63

import Theorems.Thm_neumann_remainder_tangent_scale_le_half_from_sample_bound
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (Cdev : ℝ) :
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
        tangentSamplingDeviationScale Cdev β μ₀ (max n₁ n₂) r m ≤
          (1 : ℝ) / 2 := by
  rcases neumann_remainder_tangent_scale_le_half_from_sample_bound Cdev with
    ⟨CR, hCR_pos, hsimple⟩
  refine ⟨CR, hCR_pos, ?_⟩
  intro C' hC β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hm_general
  let n : ℕ := max n₁ n₂
  have hn : 0 < n := by
    dsimp [n]
    exact lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hn_rpow_ge_one :
      (1 : ℝ) ≤ Real.rpow (n : ℝ) ((1 : ℝ) / 4) := by
    exact Real.one_le_rpow hn_real_ge_one (by norm_num)
  have hmu_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hmu_le_term :
      μ₀ ≤ μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4) := by
    nlinarith [mul_le_mul_of_nonneg_left hn_rpow_ge_one hmu_nonneg]
  have hterm_le_K :
      μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4) ≤
        max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) := by
    exact le_max_right _ _
  have hmu_le_K :
      μ₀ ≤
        max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) :=
    le_trans hmu_le_term hterm_le_K
  have hCR_nonneg : 0 ≤ CR := le_of_lt hCR_pos
  have hC'_nonneg : 0 ≤ C' := le_trans hCR_nonneg hC
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
  have hbeta_nonneg : 0 ≤ β := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_ge_one
  have htail_nonneg : 0 ≤ (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    positivity
  have hleft_le_general :
      CR * μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) ≤
        C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
              (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4))
          * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) := by
    have hCK :
        CR * μ₀ ≤
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (n : ℝ) ((1 : ℝ) / 4)) := by
      exact mul_le_mul hC hmu_le_K hmu_nonneg hC'_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hCK htail_nonneg]
  exact hsimple β hβ n r m μ₀ hn hr hμ₀ (le_trans hleft_le_general (by
    simpa [n, mul_assoc] using hm_general))
