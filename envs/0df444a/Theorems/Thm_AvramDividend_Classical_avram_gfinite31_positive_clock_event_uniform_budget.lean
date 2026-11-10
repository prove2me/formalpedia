-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite31_positive_clock_event_uniform_budget
-- name    : AvramDividend.Classical.avram_gfinite31_positive_clock_event_uniform_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T04:01:33.217966+00:00
-- url     : https://prove2.me/theorems/613b0cf1-9701-451d-aea2-2c4cae41cc93
-- title:
--   Uniform positive-stopping event budget for pre-exit approximations
-- statement:
--   For any probability space and measurable event A, a family of stopping clocks dominated pointwise by σ, and a nonnegative initial reward a, each local real-valued event budget for positive approximating clocks yields the same bound with the fixed final positive-clock event. The zero-clock reward convention does not affect these restricted integrals.
-- source:
--   Immediate necessary measure-monotonicity and zero-clock masking child of finite-cap parent 3308ae9d

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite31_positive_clock_event_uniform_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (σ : Ω → ℝ≥0) (L : ℕ → Ω → ℝ≥0)
    (hLmeas : ∀ j, Measurable (L j))
    (hLle : ∀ j ω, L j ω ≤ σ ω)
    (R : (Ω → ℝ≥0) → Ω → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hLocal : ∀ j,
      (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, R (L j) ω ∂P) ≤
      a * (P (A ∩ {η : Ω | L j η ≠ 0})).toReal) :
    ∀ j, (∫ ω in A ∩ {η : Ω | L j η ≠ 0},
      (if L j ω = 0 then a else R (L j) ω) ∂P) ≤
      a * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by sorry
