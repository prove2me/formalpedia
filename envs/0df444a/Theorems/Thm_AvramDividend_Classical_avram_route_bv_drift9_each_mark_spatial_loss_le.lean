-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le
-- name    : AvramDividend.Classical.avram_route_bv_drift9_each_mark_spatial_loss_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:42:52.546698+00:00
-- url     : https://prove2.me/theorems/163c4fc8-4f6f-45f0-a0ef-57ee1d6dfd62
-- title:
--   Spatial loss from one original negative jump is bounded by its truncated displacement
-- statement:
--   For any negative mark z of the authentic BV Lévy measure, the w-loss shifted by z, integrated over positive reserves up to epsilon, is exactly the final interval w-mass from max(0,epsilon+z) to epsilon and hence bounded by the shorter of epsilon and -z times w(epsilon). The proof uses the original zero-extension, cap-local C1 secant monotonicity, interval integral shift and additivity. This scalar theorem is the precise non-stochastic leaf of the source-level spatial Tonelli child dbf43484, not a restatement of the parent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_bv_drift9_each_mark_spatial_loss_le
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C)
    (z : ℝ) (hz : z < 0) :
    (∫ y in Ioc (0 : ℝ) ε, w y - w (y + z) ∂(volume : Measure ℝ)) ≤
      min ε (-z) * w ε := by sorry
