-- Prove2me | solution 1 for tangent_expected_deviation_core_scale_le_beta_scale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:38:29.183244+00:00
-- url     : https://prove2.me/submissions/3447fee6-1a2f-4e77-9ee4-951e98bf1556

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion
open scoped Classical BigOperators

theorem solution (Ccore : ℝ) :
    0 < Ccore →
    ∃ C : ℝ, 0 < C ∧
      ∀ (β μ₀ : ℝ) (n r m : ℕ),
        2 < β →
        tangentSamplingExpectedDeviationScale Ccore μ₀ n r m ≤
          tangentSamplingDeviationScale C β μ₀ n r m := by
  intro hCcore
  refine ⟨Ccore, hCcore, ?_⟩
  intro β μ₀ n r m hβ
  unfold tangentSamplingExpectedDeviationScale tangentSamplingDeviationScale
  have hβ0 : (0:ℝ) ≤ β := by linarith
  have hfac : μ₀ * (n:ℝ) * (r:ℝ) * (β * Real.log (n:ℝ)) / (m:ℝ)
            = β * (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ)) := by ring
  rw [hfac, Real.sqrt_mul hβ0]
  have hsY : 0 ≤ Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ)) :=
    Real.sqrt_nonneg _
  have hsb : 1 ≤ Real.sqrt β := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hstep : Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ))
      ≤ Real.sqrt β * Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ)) := by
    calc Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ))
        = 1 * Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ)) := (one_mul _).symm
      _ ≤ Real.sqrt β * Real.sqrt (μ₀ * (n:ℝ) * (r:ℝ) * Real.log (n:ℝ) / (m:ℝ)) :=
          mul_le_mul_of_nonneg_right hsb hsY
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt hCcore)
