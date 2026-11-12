-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_uniform_inner_horizon_integral_converges
-- name    : AvramDividend.Classical.avram_bvb_b21_uniform_inner_horizon_integral_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:15:27.071961+00:00
-- url     : https://prove2.me/theorems/86b854f1-46cb-45e1-ab72-ebfe7f6f5c04
-- title:
--   Integrable original uniform-grid inner horizons converge to their union
-- statement:
--   For an integrable finite-horizon source kernel, the integrals on the original genuine uniform grid's inner horizons converge to the integral over the increasing union of those horizons.
-- source:
--   Necessary horizon-strip convergence for original BV phys95 and later-ruin compensated jump integral.

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b21_uniform_inner_horizon_integral_converges
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Icc 0 T) volume) :
    Tendsto
      (fun n : ℕ => ∫ t in Icc (0 : ℝ) (T - T / ((n : ℝ) + 2)), f t)
      atTop
      (𝓝 (∫ t in ⋃ n : ℕ, Icc (0 : ℝ) (T - T / ((n : ℝ) + 2)), f t)) := by sorry
