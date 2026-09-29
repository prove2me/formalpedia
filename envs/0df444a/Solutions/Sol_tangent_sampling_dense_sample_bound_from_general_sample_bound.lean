-- Prove2me | solution 1 for tangent_sampling_dense_sample_bound_from_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T22:36:55.577733+00:00
-- url     : https://prove2.me/submissions/37d28074-028e-4a11-97ac-2859237d6ebd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hmle hμ₀ hμ₁ hsample
  let scale : ℝ := max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
  have hC'_ge_one : 1 ≤ C' := hC'
  have hμ₀_nonneg : 0 ≤ μ₀ := by linarith
  have hn_ge_one_nat : 1 ≤ max n₁ n₂ := by
    exact Nat.succ_le_iff.mp (lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂))
  have hnR_ge_one : (1 : ℝ) ≤ (max n₁ n₂ : ℝ) := by
    exact_mod_cast hn_ge_one_nat
  have hrpow_ge_one :
      (1 : ℝ) ≤ Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4) := by
    exact Real.one_le_rpow (by simpa [Nat.cast_max] using hnR_ge_one) (by norm_num)
  have hμ₀_le_arg :
      μ₀ ≤ μ₀ * Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4) := by
    exact le_mul_of_one_le_right hμ₀_nonneg hrpow_ge_one
  have harg_le_scale :
      μ₀ * Real.rpow (↑(max n₁ n₂) : ℝ) ((1 : ℝ) / 4) ≤ scale := by
    dsimp [scale]
    exact le_max_right _ _
  have hμ₀_le_scale : μ₀ ≤ scale := hμ₀_le_arg.trans harg_le_scale
  have hscale_nonneg : 0 ≤ scale := hμ₀_nonneg.trans hμ₀_le_scale
  have hscale_le_Cscale : scale ≤ C' * scale := by
    exact le_mul_of_one_le_left hscale_nonneg hC'_ge_one
  have hμ₀_le_Cscale : μ₀ ≤ C' * scale := hμ₀_le_scale.trans hscale_le_Cscale
  have hlog_nonneg : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) :=
    Real.log_nonneg (by simpa [Nat.cast_max] using hnR_ge_one)
  have hcommon_nonneg :
      0 ≤ (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
    positivity
  have hmul :
      μ₀ * ((↑(max n₁ n₂) : ℝ) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂) : ℝ))) ≤
      (C' * scale) * ((↑(max n₁ n₂) : ℝ) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂) : ℝ))) := by
    exact mul_le_mul_of_nonneg_right hμ₀_le_Cscale hcommon_nonneg
  have htarget_le_source :
      β * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
          Real.log (↑(max n₁ n₂) : ℝ) ≤
      C' * scale * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
          (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
    nlinarith [hmul]
  exact htarget_le_source.trans hsample
