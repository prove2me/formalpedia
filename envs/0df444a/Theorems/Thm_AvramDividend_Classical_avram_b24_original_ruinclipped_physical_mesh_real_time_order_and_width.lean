-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_physical_mesh_real_time_order_and_width
-- name    : AvramDividend.Classical.avram_b24_original_ruinclipped_physical_mesh_real_time_order_and_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:31:01.62948+00:00
-- url     : https://prove2.me/theorems/5c1e1864-a746-4340-9717-83e3115515d3
-- title:
--   Original ruin-clipped physical cell endpoints are ordered and NNReal time subtraction equals real elapsed time
-- statement:
--   At every cell index of the original physical grid stopped at sigma no later than horizon n, clipped time endpoints are ordered and the later point is at most n. Their nonnegative-real truncated difference coerces exactly to the ordinary real elapsed time. This is needed to connect original finite-mesh C2 Taylor and same-source Gaussian decompositions without a hidden subtraction conversion.
-- source:
--   Mathlib NNReal.coe_sub and monotonicity of min on the physical refining mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_ruinclipped_physical_mesh_real_time_order_and_width
    (n m i : ℕ) (σ : ℝ≥0) (hσ : σ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) σ
    v i ≤ v (i + 1) ∧ v (i + 1) ≤ (n : ℝ≥0) ∧
      (((v (i + 1) - v i : ℝ≥0) : ℝ)) =
        (v (i + 1) : ℝ) - (v i : ℝ) := by sorry
