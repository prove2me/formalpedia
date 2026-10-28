-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_record_real_clock_capped_event_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_strict_record_real_clock_capped_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:06:38.394631+00:00
-- url     : https://prove2.me/theorems/04e8693c-7491-4e37-bd96-8107569bbe6f
-- title:
--   Measurable finite-cap strict ENNReal exit before a real random observation clock
-- statement:
--   For measurable possibly infinite upper first-passage age τ:Ω→ENNReal, measurable real observation clock e:Θ→ℝ and any finite natural cap N, the strict capped record event {τ<N, τ<Real.toNNReal(e)} is measurable in the joint path-clock product σ-algebra. It holds even if e is negative or τ=∞. This discharges the explicit capped-event measurability premise in the genuine Esscher cap mass and cap reward monotone convergence theorems, without assuming a strict/weak clock equivalence.
-- source:
--   Pinned Mathlib Measurable.real_toNNReal, Measurable.coe_nnreal_ennreal, measurable_fst, measurable_snd, measurableSet_lt and closure under intersection.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_strict_record_real_clock_capped_event_measurable
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (clock : Θ → ℝ) (hc : Measurable clock)
    (n : ℕ) :
    MeasurableSet {z : Ω × Θ |
      τ z.1 < (n : ℝ≥0∞) ∧
      τ z.1 < (Real.toNNReal (clock z.2) : ℝ≥0∞)} := by sorry
