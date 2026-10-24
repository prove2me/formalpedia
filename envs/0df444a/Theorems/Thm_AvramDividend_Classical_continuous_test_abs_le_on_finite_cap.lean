-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
-- name    : AvramDividend.Classical.continuous_test_abs_le_on_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:49:53.990671+00:00
-- url     : https://prove2.me/theorems/ef9320ae-fc67-4a94-a675-07fc827da6ec
-- title:
--   Uniform absolute bound for a continuous HJB verification test on a finite reserve cap
-- statement:
--   A continuous real-valued verification test on nonnegative reserves attains a maximum absolute value on every compact interval [0,B]. This supplies the deterministic dominating constant for stopped HJB terminal terms at finite caps, including random localisation times.
-- source:
--   Extreme value theorem on a compact real interval in pinned Mathlib; bounded stochastic verification branch of Avram, Palmowski and Pistorius Proposition 4(i).

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

open Set

theorem AvramDividend.Classical.continuous_test_abs_le_on_finite_cap
    (w : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ContinuousOn w (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 ≤ y → y ≤ B → |w y| ≤ M := by sorry
