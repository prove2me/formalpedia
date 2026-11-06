-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:10:49.030191+00:00
-- url     : https://prove2.me/theorems/e4cef933-7d71-43f3-8ba8-fb962c575548
-- title:
--   Two original compact-reserve negative-jump coefficients have one integrable squared-difference envelope
-- statement:
--   The squared difference of the exact original negative-mark value jump coefficients for any two reserve states in a fixed compact positive band is uniformly bounded by one finite scalar times min(1,z^2). This is a pointwise source for the dominated L2 convergence of genuine predictable-grid jump coefficients.
-- source:
--   Algebraic consequence of Proved original negative-mark uniform quadratic kernel bound 90c3bdda. Use (a-b)^2≤2(a²+b²) and both original value-jump bounds. No equality in law or assumed convergence.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two original stopped-state jump coefficients share one Levy-dominated squared-difference bound. -/

theorem AvramDividend.Classical.avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ u ∈ Icc δ K, ∀ v ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        ((w (u + z) - w u) - (w (v + z) - w v)) ^ 2 ≤
          Q * min 1 (z ^ 2) := by sorry
