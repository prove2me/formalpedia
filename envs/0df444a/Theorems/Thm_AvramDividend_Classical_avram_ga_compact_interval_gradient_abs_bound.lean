-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_compact_interval_gradient_abs_bound
-- name    : AvramDividend.Classical.avram_ga_compact_interval_gradient_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T17:58:58.928587+00:00
-- url     : https://prove2.me/theorems/3a34e077-b2b4-40fa-be8f-6e1461ff4dc2
-- title:
--   Bounded classical gradient on compact real interval from continuity
-- statement:
--   If the first classical derivative of a real function is continuous on a closed interval, it has a deterministic nonnegative uniform absolute bound there. This supplies the bounded first-order coefficient needed by the stopped finite-cap Gaussian discount and full-grid source error estimates.

import Mathlib
open Set Filter Topology MeasureTheory

theorem AvramDividend.Classical.avram_ga_compact_interval_gradient_abs_bound
    (w : ℝ → ℝ) (a b : ℝ)
    (hCont : ContinuousOn (deriv w) (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      y ∈ Icc a b → |deriv w y| ≤ K := by sorry
