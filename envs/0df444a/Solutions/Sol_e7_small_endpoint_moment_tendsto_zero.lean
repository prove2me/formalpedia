-- Prove2me | solution 1 for e7_small_endpoint_moment_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:18:46.317192+00:00
-- url     : https://prove2.me/submissions/d7d7358f-972e-4655-a3eb-bec55bf70066

import Mathlib

open MeasureTheory Filter

theorem solution (G : ℝ → ℝ) (B : ℝ)
    (hbound : ∀ T : ℝ,
      ‖∫ y in (0 : ℝ)..Real.exp (-T), G y‖ ≤ B * Real.exp (-T)) :
    Filter.Tendsto (fun T : ℝ => ∫ y in (0 : ℝ)..Real.exp (-T), G y)
      Filter.atTop (nhds 0) := by
  have hB : 0 ≤ B := by
    have h := hbound 0
    have h0 : 0 ≤ B * Real.exp (-(0:ℝ)) := le_trans (norm_nonneg _) h
    simpa using h0
  have hexp : Filter.Tendsto (fun T : ℝ => Real.exp (-T)) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero
  have hbt : Filter.Tendsto (fun T : ℝ => B * Real.exp (-T)) Filter.atTop (nhds 0) := by
    simpa using hexp.const_mul B
  have hnorm : Filter.Tendsto (fun T : ℝ => ‖∫ y in (0 : ℝ)..Real.exp (-T), G y‖)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun T => norm_nonneg _) (fun T => hbound T) hbt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
