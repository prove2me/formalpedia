-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_varying_uniform_horizon_strip_vanishes
-- name    : AvramDividend.Classical.avram_bvb_b21_varying_uniform_horizon_strip_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:26:10.24209+00:00
-- url     : https://prove2.me/theorems/20403aca-821f-473a-9e7d-93fb981baf02
-- title:
--   Uniformly dominated original-grid terminal strip vanishes even for changing kernels
-- statement:
--   Nonnegative measurable time kernels varying with the grid, dominated by the same finite mark-intensity constant, have vanishing last-cell integrals on the exact shrinking terminal strip T/(n+2).
-- source:
--   Original BV finite-cap source: necessary moving-terminal-strip error bound for source-exact phys95 marked compensator quadrature.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_varying_uniform_horizon_strip_vanishes
    (T B : ℝ) (hT : 0 < T) (hB : 0 ≤ B)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, IntegrableOn (f n) (Icc (0 : ℝ) T) volume)
    (hbound : ∀ n t, t ∈ Icc (0 : ℝ) T →
      0 ≤ f n t ∧ f n t ≤ B) :
    Tendsto
      (fun n : ℕ => ∫ t in Icc (T - T / ((n : ℝ) + 2)) T, f n t)
      atTop (𝓝 0) := by sorry
