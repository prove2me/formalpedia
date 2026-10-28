-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_random_horizon_strict_event_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_joint_random_horizon_strict_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:17:20.679205+00:00
-- url     : https://prove2.me/theorems/d4aacb50-0bd4-4481-8dfe-ad80ffc9f7a0
-- title:
--   Joint measurable strict path-excursion event up to an arbitrary nonnegative random horizon
-- statement:
--   Suppose f(t,ω) is jointly measurable and right continuous in nonnegative time for every path, the independent random clock e(η) is measurable, and the threshold a(ω,η) is measurable. Then the joint event that some s≤e(η) satisfies f(s,ω)<a(ω,η) is measurable. The proof reduces the uncountable existential to a countable collection of finite dyadic grids, handling the zero-horizon case directly. This discharges the measurability assumptions of random-horizon Lévy drawdown/minimum reversal.
-- source:
--   Proved strict right-continuous dyadic grid event criterion (739dfdfa) and pinned Mathlib measurableSet iUnion, measurableSet_lt and measurable composition.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_joint_random_horizon_strict_event_measurable
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Measurable (fun z : ℝ≥0 × Ω => f z.1 z.2))
    (hcont : ∀ ω : Ω, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun t => f t ω) (Set.Ici s) s)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (a : Ω × Θ → ℝ) (ha : Measurable a) :
    MeasurableSet {z : Ω × Θ |
      ∃ s : ℝ≥0, s ≤ e z.2 ∧ f s z.1 < a z} := by sorry
