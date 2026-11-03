-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
-- name    : AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:28:16.878403+00:00
-- url     : https://prove2.me/theorems/cb439447-a20c-4328-b137-88d209abc249
-- title:
--   Canonical positive-cap C1 gradient and nonnegative zero-boundary imply global nonnegativity on every compact reserve interval
-- statement:
--   For the original Avram classical positive-cap HJB candidate, assume continuity on nonnegative reserves, w(0)>=0, C1 on the exact extended-real positive cap interior and derivative at least one there. Then w(y)>=0 on every compact [0,b] strictly below that cap, including zero. This follows from the pinned Mathlib derivative-monotonicity theorem on a convex interval and gives W7-04 the band-wide candidate nonnegativity needed by its original BV C1 discount-grid helper, without extra stochastic assumptions.
-- source:
--   Pinned Mathlib monotoneOn_of_deriv_nonneg and original cap geometry; zero-boundary plus positive gradient. Source standing process is not changed or used in this purely deterministic HJB side condition.

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
open Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∀ y ∈ Icc (0 : ℝ) b, 0 ≤ w y := by sorry
